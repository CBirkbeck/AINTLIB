# Q-lane attack blocks (beastmode-Q, 2026-07-06)

Standing rule 1: ≥3 adversarial attacks per new statement before proving. Statements
live in `ForMathlib/SpecGroupAction.lean`, `ForMathlib/InvariantLocalization.lean`,
`ForMathlib/AffineQuotient.lean`.

## T-Q1 `specSMul` + laws

- **A1 (variance sanity — is the composition law even consistent?)** `specSMul g :=
  Spec.map (toRingHom g)` with claimed law `specSMul (g*h) = specSMul g ≫ specSMul h`.
  Check on ring homs: `toRingHom (g*h) b = (g*h) • b = g • (h • b) = (toRingHom g ∘
  toRingHom h) b`, so `toRingHom (g*h) = (toRingHom g).comp (toRingHom h)`; in
  CommRingCat `ofHom (φ.comp ψ) = ofHom ψ ≫ ofHom φ`; `Spec.map (ψ ≫ φ) = Spec.map φ
  ≫ Spec.map ψ`. So `Spec.map (ofHom (toRingHom (g*h))) = Spec.map (ofHom (toRingHom
  g) ≫ ofHom' ...)` — careful: `ofHom (toRingHom g |>.comp (toRingHom h)) = ofHom
  (toRingHom h) ≫ ofHom (toRingHom g)` (CommRingCat comp order), then Spec.map flips:
  `= Spec.map (ofHom (toRingHom g)) ≫ Spec.map (ofHom (toRingHom h)) = specSMul g ≫
  specSMul h`. CONSISTENT. (Two flips cancel.) SURVIVES.
- **A2 (degenerate G)** `G = ⊥`: specSMul 1 = Spec.map (ofHom (toRingHom 1)) =
  Spec.map (ofHom id) = 𝟙 ✓ (`toRingHom_one`? verify name; else `MonoidHom.map_one`
  of toRingEquiv). Invariance/UP statements degenerate to "π is iso"? A := B^⊥ = B…
  invariantsπ = Spec.map (algebraMap B^G B) with G trivial: subalgebra ⊤?
  `FixedPoints.subalgebra R B ⊥` is all of B but as a SUBTYPE — π an iso but not `𝟙`;
  no statement claims otherwise. SURVIVES.
- **A3 (does invariance `specSMul g ≫ invariantsπ = invariantsπ` have the right
  direction?)** Ring level: need `(algebraMap A B) ≫ toRingHom g = algebraMap A B` as
  CommRingCat homs, i.e. `g • (a : B) = a` for `a ∈ A` — true by membership. Spec.map
  contravariance turns it into `specSMul g ≫ invariantsπ = invariantsπ` ✓ (NOT
  `invariantsπ ≫ specSMul g` — that composite isn't even typed: invariantsπ lands in
  Spec A, specSMul acts on Spec B). Type-checks only one way. SURVIVES.
- **A4 (orbit iff — orientation + inverse bookkeeping)** mathlib
  `exists_smul_of_under_eq`: `P.under A = Q.under A → ∃ g, g • P = Q` with `g • P`
  the POINTWISE ideal action (image of P under `g •`). Our `(specSMul g).base p =
  comap (toRingHom g) p = (g •)⁻¹(p) = g⁻¹ • p` (pointwise action of the INVERSE:
  preimage under injective g-map = image under g⁻¹). So `∃ g, (specSMul g).base x =
  y` ⟺ `∃ g, g⁻¹ • x = y` ⟺ `∃ g', g' • x = y` (g' := g⁻¹, G a group) — the iff as
  stated is equivalent to the ideal-action form; proof must swap g ↦ g⁻¹. Both
  directions of the stated iff: (←) invariance gives π ∘ specSMul g = π at points ✓;
  (→) exists_smul_of_under_eq needs `under A P = under A Q` = exactly `invariantsπ.
  base x = invariantsπ.base y` after the comap-of-algebraMap dictionary (PrimeSpectrum
  `Ideal.under` = comap). SURVIVES — with the explicit g↦g⁻¹ note.
- **A5 (universe)** B : Type u, subalgebra type in u, Spec (.of ·) : Scheme.{u} ✓;
  no ULift needed. SURVIVES.
- **A6 (SMulCommClass R B — is `smul_algebraMap` applicable for the R-triangle?)**
  `FixedPoints.subalgebra R B G` requires the section-variable `[SMulCommClass G R B]`
  (Operations.lean uses `smul_algebraMap`). Our standing hypotheses carry it. The
  over-Spec-R triangle `invariantsπ ≫ (structure map) = structure map` is NOT stated
  in T-Q1 (deferred to T-Q5's Over-S packaging) — nothing to attack. NOTE for
  skeleton: do not state R-triangles yet. SURVIVES (by omission).

## T-Q1 `invariantsπ_surjective` / `_isIntegralHom`

- **A1 (finiteness honest?)** Infinite G: invariants can be non-integral (e.g. B =
  k[x_i : i ∈ ℤ], G = ℤ shifting: B^G = k, B not integral over k). [Finite G]
  required — present in both statements. SURVIVES.
- **A2 (injectivity input)** `comap_surjective` needs `Function.Injective (algebraMap
  A B)` — algebraMap of a subalgebra = Subtype.val composed with nothing: injective ✓
  (`Subtype.val_injective`, spelled `Subalgebra.val`... verify: `algebraMap A B` for
  A a subalgebra unfolds to `A.val`; `Subtype.coe_injective`). SURVIVES.
- **A3 (does surjectivity even need IsInvariant?)** Uses only integrality +
  injectivity; `Algebra.IsInvariant.isIntegral` PROVIDES integrality and needs the
  IsInvariant instance (trivial for the honest fixed subalgebra). No circularity.
  SURVIVES.

## Verdict

T-Q1 statements as planned: SURVIVED (6+3 attacks). Orientation notes A1/A4 binding
for the proofs.

## T-Q3a `mulSemiringActionAway` + spec lemmas

- **A1 (is the action even well-defined — does `g • ·` stabilize the powers?)**
  `IsLocalization.map` needs `powers h ≤ (powers h).comap (toRingHom g)`:
  `toRingHom g (h^n) = g • h^n = (g•h)^n = h^n` by `smul_pow` + `hfix g`. Well-defined
  ONLY for invariant h — the hypothesis is load-bearing, not decorative (for
  non-invariant h, `g • ·` does not descend to Away h: e.g. B = k[x,y], G = C₂
  swapping x,y, h = x: 1/x ↦ "1/y" ∉ B_x). SURVIVES with hfix required.
- **A2 (def-not-instance)** An instance would need hfix as an instance argument —
  impossible; also two different h give different actions on defeq-different types,
  instance search could not disambiguate anyway. Precedent for def + `letI`-in-
  statement: mathlib `IsFractionRing.mulSemiringAction` + `IsGaloisGroup.
  to_isFractionRing` (Basic.lean:120). SURVIVES as def.
- **A3 (compat direction of `smul_algebraMap_away`)** claim `g • (algebraMap b) =
  algebraMap (g • b)`; from `IsLocalization.map_eq : map … (algebraMap x) =
  algebraMap (g x)` — LHS smul IS the map by definition ✓; no inverse appears (the
  action on the localization is genuinely covariant, unlike the Spec-side point
  action). SURVIVES.
- **A4 (mk' spec — denominator transport)** `g • mk' b ⟨h^n,_⟩ = mk' (g•b) ⟨toRingHom
  g h^n, _⟩` by `map_mk'`; the subtype component needs `(g•h)^n = h^n` rewriting —
  statement pins the FIXED denominator form `mk' (g•b) ⟨h^n,_⟩`. Mismatch risk is in
  the proof, not the statement. SURVIVES.

## T-Q3b fixed ⟹ invariant-over-power

- **A1 (finiteness honest?)** Infinite G counterexample sketch: B = k[x_i : i ∈ ℕ] /
  (relations making x_{i+1} = x_i/h-ish)… simpler: the proof needs ONE m with
  h^m * (g•b − b) = 0 for ALL g; per-g exponents m_g exist always, sup over
  infinite G need not. With G infinite the statement fails in general (folklore;
  invariants of localization ≠ localization of invariants for infinite groups even
  for free actions). [Finite G] present. SURVIVES.
- **A2 (which power — same n?)** Statement only claims SOME n with x = mk' b (h^n),
  b invariant — NOT that n can be taken equal to the original exponent. The h^m-
  bump changes numerator AND denominator. ∃-form correct. SURVIVES.
- **A3 (zero-divisor h)** h nilpotent ⟹ Away h trivial ⟹ every x fixed, and the
  statement demands b, n with mk' b h^n = x: b := 0, need `∀ g, g • 0 = 0` ✓
  smul_zero, and mk' 0 _ = 0 = x in the trivial ring ✓. No hidden regularity
  assumption. SURVIVES.

## T-Q3c localized inclusion (i) injective (ii) range = fixed (iii) IsLocalization

- **A1 (i — injectivity really needs val-injectivity only?)** mathlib
  `IsLocalization.Away.map_injective_iff : Injective ↔ ∀ a, f a = 0 → ∃ n, r^n * a
  = 0`. f = algebraMap A B = Subtype.val: f a = 0 → a = 0 → n := 0 works. ONE LINE.
  No G-finiteness for (i). SURVIVES.
- **A2 (ii ⊇ needs Finite, ⊆ doesn't)** range ⊆ fixed: numerator+denominator
  invariant ⟹ image fixed (map_mk' + hfix on components) — any G. fixed ⊆ range:
  = T-Q3b ⟹ [Finite G]. Statement carries [Finite G] on the ⊇/(iff) form only.
  SURVIVES.
- **A3 (iii — which algebra structure?)** `IsLocalization.Away (h : A) S'` needs
  `Algebra A S'` where S' = the fixed SUBRING of Away (h:B) under the T-Q3a action.
  Structure: codRestrict of `(algebraMap B _).comp (algebraMap A B)` into the fixed
  subring (lands there since the composite image is invariant — A3 of Q3a). If the
  wiring fights elaboration, (iii) may be DEFERRED to T-Q3 pickup and the assembly
  done through (i)+(ii) elementwise — (iii) is convenience packaging, zero
  mathematical content beyond (i)+(ii)+Q3b. Recorded as scope note. SURVIVES.

## T-Q3 (α) `RingHom.existsUnique_factor_fixedPoints_away`

- **A1 (∃!-shape justified?)** Shared-witness: uniqueness of ψ is part of the
  factorization package and both halves are consumed together at every use site
  (statement-splitting exception: single witness ψ, conjunction is `inclMap.comp ψ
  = φ` only — the uniqueness is the ∃! binder, not a second conclusion). SURVIVES.
- **A2 (injectivity direction)** ψ unique BECAUSE inclMap injective (Q3c(i)) —
  ∃!-uniqueness leg is `fun ψ' hψ' => RingHom.ext fun c => (Q3c-i) (by rw ...)`.
  Without (i) the statement would be false-ish (non-unique). Hypothesis set exactly
  right. SURVIVES.
- **A3 (fixed-image hypothesis form)** `∀ g c, awayHom hfix g (φ c) = φ c` matches
  Q3c(ii)'s RHS pointwise; hfix for ↑a instantiated by `fun g => a.2 g`. The
  alternative `Set.range φ ⊆ fixed` is the same statement — pointwise form chosen
  (usable directly). SURVIVES.

## T-Q3 (β) uniqueness `hom_ext_of_isOpenImmersion` (schematic form)

- **A1 (is the pullback the right "π over W"?)** πW := `pullback.snd π j :
  pullback π j ⟶ W`. Fibre of πW over w ∈ W = fibre of π over j(w) ≠ ∅ (π
  surjective) — surjectivity of πW = base-change stability of `Surjective` (mathlib
  instance). If instead πW were `pullback.fst`, variance breaks — pin: π along
  fst-leg, j along snd-leg ⟹ `pullback.snd (f := π) (g := j)`. SURVIVES with the
  orientation pinned.
- **A2 (degenerate W = ∅)** Then h₁ h₂ : ∅ ⟶ Y; equality holds by empty-cover
  hom_ext; the argument's per-point step quantifies over points of W — vacuous ✓.
  No hidden nonemptiness. SURVIVES.
- **A3 (why does Γ-injectivity transport to W's charts?)** The per-point argument
  restricts to a basic open D(a) ⊆ range(j) ∩ h₁⁻¹(V); the chart is
  Spec (A_a) ⟶ W (lift of the immersion along j — `IsOpenImmersion.lift` with
  range D(a) ⊆ range j) and injectivity input is Q3c(i) at a — the SAME algebra
  fact regardless of W. W only enters through open-immersion transport. SURVIVES.

## T-Q3 (γ) existence

- **A1 (the closed-set separation)** Z := π''(Uᶜ) closed needs π closed map =
  `PrimeSpectrum.isClosedMap_comap_of_isIntegral` (algebra-side, no scheme detour);
  p ∉ Z ⟺ fibre ⊆ U — uses fibres-are-orbits (T-Q1) + f constant on orbits (from
  invariance hf at POINTS: apply congrArg base to hf g). SURVIVES.
- **A2 (does D(a) ⊆ Zᶜ give π⁻¹D(a) ⊆ U?)** π⁻¹(Zᶜ) ⊆ U: x ∉ π⁻¹π(Uᶜ) ⟹ x ∉ Uᶜ.
  Preimage of basic open = basic open of the image element (comap_basicOpen).
  SURVIVES.
- **A3 (choice hygiene)** V_p, a_p, ψ_p all chosen per-point via `Classical.choice`
  — glue needs only the PROPERTIES, discharged by (β) at overlaps. No canonicity
  claim anywhere in the statement (∃ q). SURVIVES.

## T-Q4a tensor ring action / Q4b comparison map / Q4c flat / Q4d invertible

- **A1 (diamond risk on the smul)** mathlib ALREADY instances `TensorProduct.
  leftHasSMul : SMul G (A ⊗[R] R')` + `leftDistribMulAction` (Defs.lean:226/292,
  via `[DistribMulAction G A] [SMulCommClass R G A]`-shaped hypotheses). The
  MulSemiringAction instance MUST be built `{ TensorProduct.leftDistribMulAction
  with ... }` so the underlying SMul is literally the existing one — any fresh smul
  is an instant diamond. SURVIVES with this constraint pinned.
- **A2 (does g act by RING maps on the tensor at all?)** g•((a⊗r)(b⊗s)) =
  g•(ab⊗rs) = (g•ab)⊗rs = ((g•a)(g•b))⊗rs = ((g•a)⊗r)((g•b)⊗s) ✓ on pure tensors;
  bilinear extension by 2-variable tensor induction. Needs `[SMulCommClass G R A]`
  (R-linearity of the action) — without it leftHasSMul does not even apply.
  KM's setup says exactly "acts on A by R-linear ring automorphisms". SURVIVES.
- **A3 (Q4b: which base for the target fixed subalgebra?)** KM's map is
  R'-linear; `FixedPoints.subalgebra R (A ⊗[R] R') G` (R-bundled) has the same
  carrier; all bijectivity statements are bundle-independent. R-bundling chosen
  (avoids the SMulCommClass G R' wiring for now); the R'-refinement is a
  /generalise-lane flag, recorded here, NOT a statement change later (new decl if
  needed). SURVIVES.
- **A4 (Q4c flat — false without flatness?)** Yes: KM proves only ⟸; the
  standard counterexample family (torsion base change killing invariants
  mismatches, e.g. G = C₂ on A = ℤ[x]/(x²) sign-action styles over R' = 𝔽₂)
  shows ∗ can fail for non-flat R'. Hypothesis `[Module.Flat R R']` honest.
  SURVIVES.
- **A5 (Q4d — which invertibility?)** KM (4): #G invertible in R. Spelling:
  `IsUnit (Nat.card G : R)` (G finite, Nat.card). The divided trace needs the
  inverse only in R (acts on A through algebraMap). SURVIVES.

## T-Q2 freeness def + A7.1.1/A7.1.2 statements (statements-only ticket)

- **A1 (freeness def faithful to KM?)** KM: "G acts freely on A in the sense that
  for any non-zero R-algebra R', and any element g ≠ id of G, g operates without
  fixed points on the set Hom_{R-alg}(A, R')". Lean: `∀ g ≠ (1 : G), ∀ R'
  [CommRing R'] [Algebra R R'] [Nontrivial R'] (φ : A →ₐ[R] R'),
  φ.comp (g-action-as-AlgHom) ≠ φ`. "Without fixed points" = the g-precomposition
  map has no fixed φ — pointwise ∃-witness form equivalent; hom-inequality form
  chosen (cleaner). Universe: R' quantified in `Type u` (same as A — KM quantifies
  over all R-algebras; u suffices for the ∗-consequences, note recorded). SURVIVES.
- **A2 (A7.1.1 split per Tier A5)** KM's conclusion bundles (a) A finite étale
  over A^G as a G-torsor and (b) the multiplication iso `A ⊗_{A^G} A ≅ ∏_G A`.
  Two sorried single-conclusion statements: (a) as `Algebra.Etale (A^G) A ∧
  Module.Finite`? — NO ∧: split further into `Module.Finite (A^G) A` +
  `Algebra.Etale (A^G) A`; (b) `Function.Bijective (torsorMul)` where torsorMul
  x⊗y g = x * g•y (an AlgHom into `G → A`). The "G-torsor" phrasing IS (b) given
  (a) — no separate torsor-typeclass needed now. SURVIVES.
- **A3 (degenerate G = 1)** Freeness vacuous (no g ≠ 1); A = A^G; torsorMul :
  A ⊗_A A ≅ (Unit → A) ✓ true; A étale finite over itself ✓. Statements remain
  true — no hidden nontriviality needed. SURVIVES.
- **A4 (does (b)'s map even land where claimed?)** x ⊗ y ↦ (fun g => x * g•y):
  bilinear over A^G? (a·x)⊗y and x⊗(a·y) for a ∈ A^G: fun g => a x g•(y) needs
  g•(a y) = a (g•y) ✓ since a fixed. Well-defined ✓. Ring hom: pointwise product ✓
  (target Pi.ring). SURVIVES.

## T-Q5a scheme-action vocabulary + Γ-bridge

- **A1 (why a bare σ-family, not a bundled structure/MonoidHom into Aut?)**
  Consumers (T-E5's GL₂(F₃) on ℰ/Y(3)) produce morphism families; Aut-bundling
  adds iso-bookkeeping with zero payoff (IsIso is derivable: σ g ≫ σ g⁻¹ = 𝟙 from
  the two laws, as in T-Q1). The two-law family is the minimal faithful datum;
  covariant order matches specSMul (`σ (g*h) = σ g ≫ σ h`). SURVIVES.
- **A2 (stable-open def orientation)** `IsStableOpen σ U : ∀ g, (σ g) ⁻¹ᵁ U = U`.
  Preimage (not image) form — composes with `Scheme.Hom.preimage` API and needs no
  IsIso. Equivalent to image-stability for invertible σ (lemma, later if needed).
  SURVIVES.
- **A3 (the Γ-bridge action — smul or hom family?)** On `Γ(X, U)` for stable `U`:
  `g • s := ((σ g).app U-appropriately-transported) s`. The transport (preimage-U
  vs U through `IsStableOpen`) is the classic eqToHom pain point — route: define
  via `(σ g).appLE U U (le-of-stable)`: `Scheme.Hom.appLE V U (e : U ≤ f ⁻¹ᵁ V) :
  Γ(Y,V) ⟶ Γ(X,U)` avoids eqToHom entirely (e from stability equality). Action
  laws via appLE-composition lemmas. SURVIVES with appLE pinned as the route.
- **A4 (degenerate stable set)** U = ⊥: Γ = 0-ring; action trivial ✓ no
  nontriviality assumptions anywhere. SURVIVES.

## T-Q5b stable-affine refinement

- **A1 (hypothesis honest?)** `IsAffineHom (pullback.diagonal (terminal.from X))`
  (affine diagonal) is WEAKER than separated — mathlib's `IsAffineOpen.inf/iInf`
  take exactly it, and X.IsSeparated ⟹ closed-immersion diagonal ⟹ affine ⟹
  instance-derivable. Statement takes the weaker hypothesis (maximal generality,
  free). SURVIVES.
- **A2 (nonempty index)** `IsAffineOpen.iInf` requires `[Nonempty ι]`; G a group ⟹
  Nonempty G ✓ (One.nonempty instance). No gap. SURVIVES.
- **A3 (orbit hypothesis orientation)** `∀ g, σ.hom g x ∈ U` — the ORBIT through
  the covariant σ (σ g x for all g covers the orbit; g := 1 gives x ∈ U). The
  refinement V := ⨅_g (σ g)⁻¹ᵁ U: x ∈ V ⟺ ∀ g, σ g x ∈ U ✓ matches. Stability:
  (σ g)⁻¹ᵁ V = ⨅_h (σ(g*h))⁻¹ᵁ U = V by mul-reindex (group!). SURVIVES.
- **A4 (Finset.inf vs iInf spelling)** ⨅-Opens over a Finite index has
  set-coe = ⋂ only through `Opens`-completeness quirks; route via lattice-only
  algebra (le_antisymm + le_inf/inf_le for stability; membership via the ⨅-mem
  characterization or explicit fun-of-g). Pinned: use `⨅ g : G` (matches
  `IsAffineOpen.iInf`'s binder form directly). SURVIVES.

## T-Q5c leaf: `exists_mem_basicOpen_subset_of_stable` (stable-basic basis)

- **A1 (statement scope)** Set-level stable open U of `Spec B` + point: produce
  `a : Bᴳ` with `x ∈ D(↑a) ⊆ U`. D(↑a) is automatically stable (↑a invariant ⟹
  its non-vanishing locus is orbit-saturated — NOT claimed in the statement, no
  need). SURVIVES.
- **A2 (stability form)** `∀ g x, x ∈ U → specSMul g x ∈ U` — the ⊆-form (weaker
  than =-form, sufficient: only "fibre ⊆ U" is used, which needs orbits INTO U).
  For a GROUP the two are equivalent; take the weak form (easier for consumers).
  SURVIVES.
- **A3 (reuse)** Proof is the closedness separation from `exists_chart_descent`
  verbatim minus the chart: fibre-of-π(x) = orbit ⊆ U (T-Q1 orbit lemma +
  stability), Z := π''(Uᶜ) closed (integrality), π(x) ∉ Z, basic open of Bᴳ
  inside Zᶜ, pull back. Same [Finite G] necessity. SURVIVES.

## T-Q5c open-immersion-ness of localQuotientMap (route note, 2026-07-06T20:30Z)

Route of record: `IsOpenImmersion.of_stalk_iso` (the same tool mathlib uses for the
localization chart instance):
- (i) base is an open embedding: injective (lift along surjective π^W, compare
  V-orbits = W-orbits since W stable — fibres-are-orbits both levels) + OPEN MAP
  (every open of Q_W is π^W(stable open) by quotient-map + saturation; its image is
  π^V(same stable open), open by `isOpen_image_invariantsπ_of_stable` transported
  through isoSpec) ⟹ `IsOpenMap.isOpenEmbedding` variant with injectivity.
- (ii) stalk isos: at q = π^W(w), both stalks are the filtered colimit of sections
  over INVARIANT BASIC opens around the orbit (basis lemma
  `exists_mem_basicOpen_subset_of_stable`), and on invariant basics the two sides
  agree by T-Q3c ((Γ_f)ᴳ = (Γᴳ)_f) — compare via `IsLocalization.AtPrime`
  uniqueness or colimit-cofinality. THE algebra is done; this leaf is colimit
  plumbing.
- Alternative if stalk-plumbing fights: both Q_W and the image-open of Q_V satisfy
  the categorical-quotient UP of W (uniqueness via
  invariantsπ_hom_ext_of_isOpenImmersion at j := image-inclusion) ⟹ canonical iso;
  then IsOpenImmersion (iso ≫ open-inclusion).

## REFINEMENT (2026-07-06T20:40Z, supersedes the of_stalk_iso preference):
`exists_invariantsπ_lift_of_isOpenImmersion` — the j-RELATIVE existence

Statement: for an open immersion `j : Q' ⟶ Spec Bᴳ` and `f : pullback π j ⟶ Y`
invariant under the pulled-back action, `∃ q : Q' ⟶ Y, pullback.snd π j ≫ q = f`.
Proof = T-Q3's existence VERBATIM with the per-point charts chosen INSIDE
`range j` (the basis lemma already produces basics inside any open). Payoff:
- at j := 𝟙: re-derives exists_invariantsπ_lift;
- at j := image-open inclusion: gives the UP of `π^V(W)` ⟹ the canonical iso
  `Q_W ≅ π^V(W)-open` ⟹ `IsOpenImmersion (localQuotientMap …)` with NO stalk
  plumbing;
- at T-Q5d: the global existence glue reuses it per stable-affine chart.
Mirror of the already-proven `invariantsπ_hom_ext_of_isOpenImmersion` — the two
j-relative statements together say `π` is an effective epi stable under open
restriction, which IS the descent content of Loeffler 3.6.1.

## T-Q5 (α) IsOpenImmersion (localQuotientMap) — attack block (2026-07-07 pickup)

- **A1 (window well-formed)** `windowHom := X.homOfLE hWV ≫ hVa.isoSpec.hom` is an
  open immersion (homOfLE-instance ≫ iso); its range is the "W-window" in
  Spec Γ(V). Stability under the Γ(V)-specSMul: pointwise from the two proven
  squares (resLE_homOfLE + resLE_isoSpec_hom). No new math. SURVIVES.
- **A2 (saturation)** range fst_{π,j₀} = π⁻¹(imageOpens) = π⁻¹(π(window-range)) =
  window-range needs stability (A1) + fibres-are-orbits — exactly the hsat idiom
  of isOpen_image_invariantsπ_of_stable. SURVIVES.
- **A3 (inverse construction honest?)** q from the KEYSTONE at j₀; the two
  inverse laws are pure UP-uniqueness (Q_W-side absolute hom_ext; Q'-side
  j₀-relative hom_ext) given the three composition facts π^W ≫ m₀ = iso.hom ≫ snd,
  snd ≫ q = f₀, f₀ = iso.inv ≫ π^W. Any failure here is a wiring bug, not a
  math gap. SURVIVES.
- **A4 (degenerate W = ⊥)** Q_⊥ = Spec of invariants of the zero ring = empty
  scheme; imageOpens = ∅; everything holds vacuously; no nontriviality used.
  SURVIVES.

## T-Q6 attack blocks (2026-07-06T22:55Z)

### `ModuliProblem.simul P δ` (pointwise product presheaf)
- **A1 (universe)**: `P.obj X × δ.obj X : Type u` — fine, both factors land in
  `Type u`; no `ULift` needed. PASS.
- **A2 (functoriality)**: `map (f ≫ g) = map f ≫ map g` componentwise via
  `Prod.map` — `P.map_comp`/`δ.map_comp` pointwise; `Prod.ext` closes. PASS.
- **A3 (wrong-shape risk: should it be the categorical product `P ⨯ δ`?)**: the
  categorical product in `(EllObj R)ᵒᵖ ⥤ Type u` IS computed pointwise, but its
  mathlib packaging (chosen limits) makes `obj`-values opaque
  (`limit (pair P δ) |>.obj`); KM's proof constantly reads pairs `(α, β)`.
  Hand-rolled product with `obj := P.obj X × δ.obj X` is defeq-transparent; if a
  consumer ever needs the `Limits.prod` comparison it is a one-iso lemma. Choice
  of record: hand-rolled. PASS with note.
- **A4 (naming)**: KM says "simultaneous problem (𝒫,δ)" — name `simul`, keep KM
  order (P first, δ second; the G-action will live on the SECOND factor).

### `simul_representable` (KM 4.7 step (i): 𝕸(𝒫,δ) = 𝒫_{E/𝕸(δ)})
- **A1 (truth as stated)**: KM p. 112 asserts exactly this with 𝒫 relatively
  representable and δ representable. The proof needs the NATURALITY clause of
  `RelativelyRepresentable` (restriction-compat of the `eqv`s) — present in the
  project def since T-E3. No affineness needed for bare representability (the
  affineness conclusion "𝕸(𝒫,δ) affine over 𝕸(δ)" is a SEPARATE statement, cut
  only when T-Q6d's quotient step demands it). PASS.
- **A2 (the hidden lemma)**: transporting `P`-values along the tautological
  cartesian square: for `u : Y ⟶ Xδ` in `Ell/R`, need `Y ≅ Xδ.pullbackAlong
  u.baseHom` (comparison of Y.curve with the CHOSEN pullback). This is T-Q6b —
  `EllHom.isPullback` + `IsPullback.isoPullback` + `zero_w`. Without it the
  ∃-chain does not compose. Cut FIRST.
- **A3 (choice hygiene)**: `RelativelyRepresentable` is an ∃-Prop; the
  representing `Z` per `X` comes via `choose` — noncomputable, fine (the
  STATEMENT `(P.simul δ).Representable` is a Prop; no data leaks).
- **A4 (adversarial: Loeffler's "converse not quite true" remark)**: that remark
  is about P̃ vs P (Sch/R-side), NOT about simul-representability. Not a
  counterexample to this statement. PASS.

### T-Q6b `isoPullbackAlong` (every EllHom is cartesian)
- **A1 (data honesty)**: the iso is DATA (an `Iso` in `Ell/R`) — must be a real
  def; both directions + hom_inv_id/inv_hom_id. Route: `EllHom.isPullback u`
  gives `IsPullback u.top Y.curve.π Xδ.curve.π ...`? — CHECK the exact field
  shape before writing (the file defines `EllHom` with `top`, `isPullback`,
  `zero_w`); the comparison to `pullbackAlong` (which uses
  `EllipticCurve.baseChange` = `Limits.pullback`) is
  `IsPullback.isoPullback`-vs-`limit.cone` — same mk-pt friction class as the
  T-Q5 vPullbackCone fight; budget a cleanly-typed-∃ repackaging if rw-motives
  bite.
- **A2 (zero-section compat)**: an `Ell/R`-iso needs `zero_w` BOTH directions;
  inverse direction zero_w follows from forward + iso-cancellation — prove via
  `IsPullback.hom_ext` on the pullback, not by inverting rectangles by hand.
- **A3 (base leg)**: the comparison should be OVER `𝟙 Y.base` (baseHom = 𝟙) —
  check `pullbackAlong u.baseHom` has base `Y.base` definitionally (it does:
  `base := T`). PASS.

### T-Q6d statements (RelRepData / TorsorData / Scholie) — 2026-07-07T01:20Z
- **A1 (RelRepData = honest bundling?)**: fields Z/f/eqv/nat are EXACTLY the
  ∃-chain of `RelativelyRepresentable` (T-E3 def) — no strengthening, no loss;
  bridge lemma `relativelyRepresentable_iff_nonempty_relRepData` is
  choice-only. PASS.
- **A2 (equivariance convention)**: `eqv g ⟨h.1 ≫ σZ.hom γ, _⟩ = (φ γ).hom.app _
  (eqv g h)` — precomposition on the Z-side vs `φ γ`-hom on the value side.
  Attack: γ ↦ γ⁻¹ flip risk. Verdict: σZ is DATA quantified inside TorsorData,
  so either convention is satisfiable by reindexing (σZ ↦ σZ ∘ inv); the
  statement is honest under either; convention pinned = this one, chosen to
  match `SchemeAction`'s covariant `hom` and KM's "the S-scheme δ_{E/S} is a
  G-torsor" (left action on points by postcomposition-of-action =
  precomposition on classifying maps). Consumers must NOT assume the other
  convention silently — bridge lemmas at instantiation time.
- **A3 (torsor comparison map)**: `∐_G Z ⟶ Z ×_{X.base} Z`, `γ ↦ (σZ γ, 𝟙)` —
  matches Stack.lean's `levelledCurve_descent_of_torsor` htorsor shape
  (in-project precedent, adversarially fixed 2026-07-05 there). Surjectivity
  of f is NOT separately demanded: for a G-TORSOR KM's "finite etale G-torsor"
  over the base includes f fppf-cover; ATTACK: over ∅-fibres the comparison
  being iso is vacuous, so a torsor in this weak sense can have empty fibres
  (Legendre over ℤ: concentrated over S[1/2]!). KM p. 111: "concentrated over
  S[1/2], over which it is a torsor" — the ENGINE is stated over a base where
  the axioms hold with honest content; f Surjective ADDED as a field to make
  "torsor" mean torsor (KM applies the engine only over ℤ[1/N] where it holds).
- **A4 (Scholie hypotheses honesty)**: KM 4.7.0 needs 𝒫 affine over (Ell) and
  M(δ) affine (axiom 1). Both carried as explicit hypotheses (IsAffineHom on a
  P-rel-rep datum's f, IsAffine on the δ-representing base). Loeffler drops
  affineness — T-E5 statement-risk already flagged on the board; the ENGINE
  stays KM-honest.
- **A5 (freeness statement)**: scheme-level freeness = `t ≫ hom g = t → g = 1 ∨
  IsEmpty T`? NO — KM: free on nonempty T only makes sense pointwise:
  statement: g ≠ 1 → no fixed T-point with T nonempty, i.e.
  `t ≫ hom g = t → IsEmpty T`. Attack: IsEmpty vs ¬Nonempty — same;
  formulation quantifies T arbitrary (not just Spec R'), STRONGER than KM's
  ring-points form but what SGA III V 4.1 needs; provable since a fixed
  T-point restricts to fixed geometric points. Statement stays; proof is the
  θ(g)-rigidity argument (KM p. 113) — sorried this session with route banked.

### T-W3b full-faithfulness ATTACK FINDING (2026-07-07T03:50Z)
The naive claim "trivialization `ActionGroupoid σ S ⥤ TorsorPair σ S` is fully
faithful" is FALSE:
- **S = ∅**: `Hom_{[X/G]}(t, t') = {g // t ≫ σ g = t'} = G` (all conditions
  vacuous), but `Hom(triv t, triv t')` = maps `∅ ⟶ ∅` = singleton. Not faithful
  for `|G| > 1`.
- **S disconnected**: a torsor-pair endomorphism of `∐_G S` may left-translate
  different connected components by different group elements; only single
  elements come from the functor. Not full.
Verdict: state full-faithfulness only for connected nonempty `S` (or state the
honest general comparison at stackification level — the prestack [X/G] is not
even fppf-separated, which is exactly WHY stackification appears). Board text
corrected. The trivialization FUNCTOR itself is still total (no hypotheses);
only the equivalence claims carry connectivity hypotheses.
