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
