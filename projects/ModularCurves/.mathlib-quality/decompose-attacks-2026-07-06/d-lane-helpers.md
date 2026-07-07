# Adversarial attack blocks — D-lane Wave-0 helper declarations (beastmode-D2)

New helper statements get their block here at statement time (v5 rule; standing
rule 1). Format mirrors `level-structures.md`.

### T-D24: rank additivity in short exact sequences (ForMathlib/FinrankExact.lean)

Statements: (a) `Function.Exact.nonempty_linearEquiv_prod_of_projective`:
`0 → M →f→ N →g→ P → 0` exact with `[Module.Projective R P]` ⟹
`Nonempty (N ≃ₗ[R] M × P)`; (b) `Module.finrank_eq_add_of_exact`:
`finrank R N = finrank R M + finrank R P` for `M`, `P` finite free; (c)
`Module.rankAtStalk_eq_add_of_exact`: pointwise
`rankAtStalk N p = rankAtStalk M p + rankAtStalk P p` for `M`, `P` finite flat.

- Attacks: [1] **Hypothesis necessity / falsity probes**: (b) fails without
  freeness of the OUTER terms even over ℤ? Take `0 → ℤ →2→ ℤ → ℤ/2 → 0`: P = ℤ/2
  not free; finrank ℤ (ℤ/2) = 0 (junk: no basis, finrank of non-free f.g. torsion
  = 0), additivity would claim 1 = 1 + 0 ✓ accidentally true BUT the split (a)
  fails (ℤ ≄ ℤ × ℤ/2) — so (b) genuinely needs P projective for the route, and
  the free hypotheses are the honest scope (KM's modules are finite locally free).
  For (c): M, P finite flat localize to finite free over the local ring — the
  hypotheses are exactly what the proof consumes; N needs NOTHING (its rank is
  computed through the splitting) — adversarially minimal. SURVIVES.
- [2] **Junk-value coherence**: `finrank`/`rankAtStalk` are ℕ-valued junk-0 on
  non-free/non-finite modules; all statements only ever evaluate them on
  free-or-localized-free modules (b: M, P, and N ≅ M × P which IS free+finite;
  c: localizations at a prime of finite flats are finite free). No statement
  reads a junk value. SURVIVES.
- [3] **Triviality/degenerate cases**: `Subsingleton R` — every module is
  subsingleton, all ranks 0, both sides 0 ✓ (finrank_prod route must not need
  `Nontrivial R`; verify at build — if `Module.finrank_prod` requires
  StrongRankCondition-with-Nontrivial, case-split or add the instance mathlib
  requires and record). `n = 0` SES (`M = P = 0`): N ≅ 0 ✓. `Exact` with junk
  zero maps: hf/hg exclude pathologies. SURVIVES (with the Subsingleton check
  discharged at build time).
- [4] **Not-in-mathlib**: greps `finrank_eq_add`/`finrank_add_finrank_eq`/
  `rankAtStalk.*add` → only `rankAtStalk_prod` (FreeLocus.lean:313) and the
  DivisionRing-only Euler-characteristic lemma
  (`Module.sum_neg_one_pow_finrank_eq_zero_of_exact`, Algebra/Exact/Sequence.lean
  — fields only); `Exact.splitSurjectiveEquiv` needs a SECTION, mathlib never
  composes it with `projective_lifting_property`. Genuine gaps; (a)–(c) all
  upstream candidates. SURVIVES.
- [5] **Orientation/convention**: SES written as `(f, g)` with `Injective f`,
  `Surjective g`, `Function.Exact f g` — mathlib's standard encoding (no
  ComplexShape machinery); conclusion sides `N = M + P` ordered sub-then-quotient
  matching `rankAtStalk_prod`'s `M × N` order. SURVIVES.
- Verdict: **SURVIVED** (statement package as designed).

### T-D29: `Algebra.charpoly_lmul_eq_norm` (ForMathlib/CharpolyNorm.lean)

Statement: for `B` a finite free `R`-algebra and `b : B`,
`(Algebra.lmul R B b).charpoly = Algebra.norm R[X] ((X : R[X]) ⊗ₜ[R] 1 - 1 ⊗ₜ[R] b)`
(element of the `R[X]`-algebra `R[X] ⊗[R] B`).

- Attacks: [1] **Statement-fidelity / the wrong reading**: the v4 board bullet's
  loose spelling `LinearMap.charpoly f = Algebra.norm R[T] (T•1 − f⊗1)` admits a
  general-endomorphism reading (`f : End R M`, element of `End R[X] (R[X]⊗M)`),
  which is FALSE: for `g ∈ End(V)`, `Algebra.norm (End V/K) g = det(g)^{dim V}`
  (lmul on End is dim-V copies of g), so the RHS would be `charpoly`-like only
  after an n-th root. KM 1.8.2's own text ("the characteristic polynomial of
  f ∈ B is just the norm of T−f relative to B⊗R[T]/R[T]") fixes `f ∈ B` an
  ALGEBRA element and the endomorphism = multiplication by it. The formalised
  statement takes `Algebra.lmul R B b` — the faithful reading. REJECTED-reading
  documented, statement SURVIVES.
- [2] **Convention (sign/monic)**: mathlib `charpoly = det (charmatrix) =
  det(X•1 − A.map C)` is monic-in-X, matching `norm(X⊗1 − 1⊗b)` whose matrix is
  `X•1 − (leftMulMatrix b).map C` — same matrix, no `(−1)ⁿ` skew (both are KM's
  `det(T − f)`). SURVIVES.
- [3] **Degenerate cases**: `B = 0` (rank 0): both sides are empty determinants
  `= 1` (charpoly over the zero module; `R[X] ⊗ 0 = 0`, norm on the zero algebra
  is det of the zero-module endomorphism `= 1`). `b = 0`: LHS = charpoly of 0-map
  `= Xⁿ`; RHS = `norm(X ⊗ 1) = Xⁿ · norm(1⊗1) = Xⁿ` ✓. Free-of-rank-0 and
  `Subsingleton R` cases carried by the same determinant conventions. SURVIVES.
- [4] **Hypotheses**: `[Module.Free R B] [Module.Finite R B]` required by
  `LinearMap.charpoly` (defined via `chooseBasis`); the norm side needs no extra
  instances (basis via `Module.Basis.baseChange`; `Module.Free/Finite` of
  `R[X] ⊗[R] B` over `R[X]` not even needed in the statement). `CommRing B` kept
  to match the KM consumer (T-D30); relaxation to `Ring B` is a cleanup-lane
  question, not load-bearing. SURVIVES.
- [5] **Not-in-mathlib**: 4 searches (charpoly-grep in RingTheory/Norm/*;
  global `charpoly∩norm` grep; `def charpoly` enumeration; instance/bridge grep +
  `LinearMap.charpoly_baseChange` inspection — that lemma is base-change
  functoriality, not the norm bridge). Genuine gap; upstream candidate. SURVIVES.
- Verdict: **SURVIVED** (statement as formalised; loose board spelling refined
  on the board at claim time).

### T-D3b: `IdealSheafData` multiplicative structure — **RESOLVED: MATHLIB HAS IT**

2026-07-06T11:40Z (beastmode-D2): at the current pin (11b908e5cdd9), mathlib's
`Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean` §Semiring (lines 400–460) already
provides everything T-D3b planned and more: `Zero`/`One`/`Add`/`Mul`/`Pow ℕ`
instances (mul via `mkOfMemSupportIff` with support `I.supportSet ∪ J.supportSet`),
`IdemCommSemiring X.IdealSheafData`, `IsOrderedRing`, simp pins `ideal_mul`,
`support_mul`, `ideal_pow`, `top_mul`, `mul_top`, `bot_mul`, `mul_bot`, distributivity
(`mul_inf`/`inf_mul` — note: names say inf, content is `⊔`), and the simp-normal-form
lemmas `zero_eq_bot`/`one_eq_top`/`add_eq_sup`. Also `radical` API further down.
The daily-bump gift postdates the D-off.2 sub-plan. T-D3b closes with NO project
code; T-D3's `sectionsDivisor` fold should use `∏` (Finset.prod) directly against
these instances. My drafted duplicate (attack block below, kept for the record) was
deleted before commit.

Original block (superseded, kept for audit):

Statements: `instance : Mul (IdealSheafData X)` with
`(I * J).ideal U = I.ideal U * J.ideal U`; `instance : CommMonoid (IdealSheafData X)`
with `1 = ⊤`; simp pins `ideal_mul`, `ideal_one`; order lemma `mul_le_inf`.

- Attacks: [1] **Gluing well-definedness**: the sheaf condition
  `(ideal U).map res = ideal (affineBasicOpen f)` must survive the product —
  localization commutes with ideal products: mathlib `Ideal.map_mul`
  (Maps.lean:644, protected, RingHomClass form ✓ applies to the CommRingCat hom) +
  the two factors' own `map_ideal_basicOpen`. No radical/closure correction needed —
  `Ideal.map` of a product is exactly the product of maps. SURVIVES.
- [2] **Convention/orientation**: divisor SUM = ideal PRODUCT (KM 1.1.2 local form
  `fg`), so the fold for `sectionsDivisor` (T-D3) needs `CommMonoid`, not lattice
  ops; unit = empty divisor = unit ideal sheaf = `⊤`, matching mathlib's
  `Ideal.one_eq_top` convention (NOT `⊥` — the subscheme order is reversed to the
  ideal order). Degree additivity (later, T-D24 consumer) is against the SES on
  `A/fgA` — consistent with product, NOT with `⊓` (which loses multiplicity on
  non-radical overlaps: for `D + D` at a point, `f²` vs `f`). This is exactly why
  `mul ≠ inf` is load-bearing. SURVIVES.
- [3] **Instance collision / diamond**: mathlib's `IdealSheafData` carries only
  `PartialOrder`/`CompleteLattice`/`OrderTop`/`OrderBot` (checked
  IdealSheaf/Basic.lean @ pin 11b908e5cdd9) — no `Mul`/`One`/`Monoid` instance to
  clash with; `1 = ⊤` introduces a `One` whose interplay with the lattice `⊤` is
  definitional (`one := ⊤`), so no propositional-diamond. Adding instances to a
  mathlib type from ForMathlib: OURS register, upstream candidate, delete on
  upstream landing. SURVIVES.
- [4] **Degenerate cases**: `Γ(X,U) = 0` (empty U / empty X): all ideals equal,
  product collapses — fine. `supportSet`: omitted ⟹ structure default
  `⋂ U, zeroLocus (ideal U)`; support of `I*J` agrees set-theoretically with
  `I ⊓ J` (same radical), so the default is the honest support — consistent with
  mathlib's own `SemilatticeInf` instance which also uses the default. SURVIVES.
- Verdict: **SURVIVED** (statement-level); proofs are 1–3-liners against
  `Ideal.map_mul` / pointwise `CommSemiring Ideal` lemmas.

### T-D25 / T-D26 findings of record (2026-07-06T13:25Z, beastmode-D2)

**T-D25 RESOLVED-BY-MATHLIB** (no statement needed, no attack block needed):
`Module.algebraMap_bijective_iff_rankAtStalk` + alias (Flat/Rank.lean:120–129,
finite flat algebra) and `Module.Free.bijective_algebraMap_of_finrank_eq_one`
(Trace.lean:399, free rank-1, [Nontrivial R]). Both directions of KM 1.2.7's
"invertible-module algebra is R".

**T-D26 algebra engine mathlib-present**:
`Module.rankAtStalk_eq_zero_iff_subsingleton` (FreeLocus.lean:303) +
`Module.support_eq_empty_iff` (Support.lean:119). Divisor-level wrapper deferred
into T-D15 (needs the Scheme.Hom.finrank ↔ RingHom.finrank ↔ rankAtStalk affine
dictionary; `RingHom.finrank` exists at Flat/Rank.lean:138 — bridge half-built
upstream already).

### Plugin update incorporated (2026-07-06T13:45Z, beastmode-D2)

`references/statement-splitting.md` landed (one conclusion per declaration;
∧-chains and numbered source parts born split; assembly lemmas must be one-line
anonymous constructors with a real consumer; shared-witness existentials NOT
split — witness-def + per-property specs preferred; mutual-induction bundles as
private aux + projections; ≥3-way equivalences via TFAE). Audit of D-lane
statements delivered so far: T-D13 (one equation), T-D24 (three single-conclusion
lemmas — the split/finrank/rankAtStalk trio is exactly the born-split shape),
T-D29 (one equation) — all conform. Board-frozen skeleton statements checked
against trigger shapes: `exists_incidenceLocusEQ`'s `∧` sits under an iff inside
`∃ Z, ∀ T` with a SHARED witness Z — non-trigger (exceptions 1+3). All future
D-lane helper statements and sub-tickets born split per the reference.

### T-D27 (i): `sectionVanishingIdeal_eq_span_coord_coord` (Incidence.lean §ZeroLocus)

Statement: for a tower `R → B ↷ M` (`[Algebra R B] [Module B M]
[IsScalarTower R B M]`), `c : Module.Basis κ R B`, `b : Module.Basis ι B M`:
`sectionVanishingIdeal R M σ = Ideal.span (Set.range fun p : κ × ι =>
c.coord p.1 (b.coord p.2 σ))`. Single conclusion ✓ statement-splitting-conformant.

- Attacks: [1] **Tower coherence**: without `[IsScalarTower R B M]` the R-module
  structure on M is unrelated to B and the statement is junk-false; with it, the
  R-structure is the restriction — `Basis.smulTower` (AlgebraTower.lean:126)
  requires exactly this configuration, and `smulTower_repr` gives
  `(c.smulTower b).repr σ (j,i) = c.repr (b.repr σ i) j`, which is verbatim the
  RHS generator set. SURVIVES.
- [2] **Argument-order convention**: mathlib's `smulTower (b : Basis ι R S)
  (c : Basis ι' S A)` takes the BASE basis first; our `c` (R-basis of B) plays
  that role. Index pair `κ × ι` (base × top) matches `smulTower`'s `ι × ι'`.
  Misreading the order would produce a type-correct but WRONG generator set
  (`b.coord` applied to elements of B) — caught because `b.coord p.2 σ : B` and
  `c.coord p.1 : B →ₗ R` compose only in the stated order. SURVIVES.
- [3] **Consumer fidelity (KM count)**: for T-D16(3), the descended condition has
  rank_B(M)·rank_R(B) = 1·(deg D)² equations — matches KM 1.3.7's "(deg D)²"
  via "the vanishing on W of a single function is equivalent to the vanishing on
  S of its coordinates". Degenerates: B = 0 (κ empty ⟹ both sides ⊥ on the
  zero module), σ = 0, ι empty — all coherent junk-⊥. SURVIVES.
- [4] **Scope split**: deliverable (ii) (base-change vanishing bridge
  `σ ⊗ 1 = 0 ↔ I(σ) ≤ ker`) deferred into T-D14/T-D16 whose ⦃T⦄-statements pin
  the tensor spelling — same scoping as T-D26's wrapper. Recorded on the board.
- Verdict: **SURVIVED**.

### T-D31: reduced-ring separation by field-valued homs (ForMathlib/ReducedSeparation.lean)

Statements (born split): (i) `IsReduced.eq_zero_of_forall_ringHom_field`:
`[CommRing A] [IsReduced A]`, `(∀ (K : Type u) [Field K] (φ : A →+* K), φ a = 0) → a = 0`;
(ii) `IsReduced.eq_of_forall_ringHom_field`: same quantifier with `φ a = φ b → a = b`
(one-line corollary via `sub_eq_zero` + `map_sub`).

- Attacks: [1] **Reducedness necessity**: false without it — `A = k[ε]`, `a = ε`:
  every hom to a field kills ε (nilpotents die in fields/domains), yet ε ≠ 0.
  The hypothesis is load-bearing and minimal. SURVIVES.
- [2] **Prime-vs-maximal**: the proof needs ⋂ primes = nilradical
  (`nilpotent_iff_mem_prime`); restricting the family to maximal-residue fields
  would prove the FALSE Jacobson-radical variant (local domain: ⋂ max ⊋ 0).
  The fraction field of `A⧸J` for every PRIME J is exactly the needed family,
  and it lives in the same universe u — the `∀ K : Type u` quantifier is
  sufficient (attack: a smaller quantifier universe would break the internal
  instantiation; same-u matches T-D2's consumer which quantifies `K : Type u`).
  SURVIVES.
- [3] **Alg-closed strengthening**: KM 1.9.2 checks at geometric (alg. closed)
  points; our field-level family is FINER (more homs available ⟹ weaker
  hypothesis per instance... careful: hypothesis quantifies over ALL fields, so
  field-version hypothesis is STRONGER than alg-closed-version hypothesis).
  Consumer check: T-D2's RHS quantifies over all fields `K` with `[Algebra R K]`
  — matches exactly; no alg-closed gap enters the Lean route (KM's geometric
  points are an informal-side strengthening we do not need). SURVIVES.
- [4] **Degenerates**: `A = 0` (trivial ring): reduced ✓, every a = 0 ✓ statement
  vacuous-true; fields are nontrivial so no hom A → K exists when... A = 0 has
  no ring hom to any field?? `A →+* K` with A trivial: φ 1 = 1 forces K
  trivial — no field K admits it, hypothesis vacuously true, and a = 0 holds in
  the trivial ring ✓ coherent. `a` a unit: hypothesis fails at any K (φ a unit
  ≠ 0) unless no homs exist — Spec A ≠ ∅ for A ≠ 0 so some prime/hom exists ✓.
  SURVIVES.
- [5] **Not-in-mathlib**: `IsReduced (MvPolynomial σ R)` instance EXISTS
  (Nilpotent.lean:55) — that half is mathlib-present; the separation lemma
  absent (greps `eq_zero_of_forall.*field` / `forall_ringHom` / nilradical
  consumers — none state the field-hom form). Upstream candidate. SURVIVES.
- Verdict: **SURVIVED** (both statements; single-conclusion each ✓
  statement-splitting-conformant).

### T-D32: fibrewise bijectivity detection (ForMathlib/BijectiveResidueField.lean)

Statements (born split): (a) `IsLocalRing.surjective_of_surjective_lTensor_residueField`
([Module.Finite R N] only); (b) `IsLocalRing.bijective_of_bijective_lTensor_residueField`
([Finite M] [Finite N] [Flat N]); (c) global
`LinearMap.bijective_of_forall_bijective_lTensor_residueField` (fibres `φ.lTensor
J.ResidueField` at every maximal J).

- Attacks: [1] **Hypothesis necessity**: (a) N finite is Nakayama's requirement (fails
  for non-fg: R = ℤ_(p), N = ℚ, φ = 0 from M = 0: κ⊗ℚ = 0 so fibre-surjective, φ not).
  (b) N flat is what makes free-over-local fire; injectivity genuinely needs the
  splitting (nonfree N: R = k[x]/x², M = k = R/x, N = R, φ = x·incl? fibre-inj can
  fail/hold accidentally — the split-iff is the honest engine). N ≠ hypothesis-free:
  drop Flat N and take R = k[x]/x², M = R, N = k, φ = quotient: κ⊗φ : k → k identity
  bijective, φ not injective ⟹ Flat N load-bearing ✓. [2] **Maximal vs prime
  quantifier** (c): maximals suffice for DETECTION (bijective_of_isLocalized_maximal);
  the consumer (T-D6) has fibre-isos at all points ⟹ maximals instantiate. Converse
  direction deliberately NOT stated (statement-splitting assembly test: no consumer).
  [3] **Spelling**: fibres as `lTensor J.ResidueField` with `Ideal.ResidueField` an
  ABBREV for `IsLocalRing.ResidueField (Localization.AtPrime J)` — the local lemma at
  Rⱼ needs κ(Rⱼ) which is DEFINITIONALLY J.ResidueField; no transport. The localized
  map is identified with `φ.baseChange Rⱼ` by `IsLocalizedModule.ext` + `map_comp`
  (defining property) + `TensorProduct.isBaseChange` instance via
  `isLocalizedModule_iff_isBaseChange`; fibre comparison by the
  `cancelBaseChange` square proven on pure tensors (2-level induction). [4] **Det
  route rejected**: mathlib `LinearMap.det` is endo-only; φ connects different
  modules — recorded in module docstring so nobody re-attempts it. [5]
  **Not-in-mathlib**: the Nakayama toolkit exists (map_tensorProduct_mk_eq_top,
  split_injective_iff_lTensor_residueField_injective, bijective_of_isLocalized_maximal)
  but no composed fibrewise-detection statement (greps: surjective/bijective ∩
  residueField, of_isLocalized_maximal consumers). Upstream candidates ×3. SURVIVES.
- Verdict: **SURVIVED** (single-conclusion each; statement-splitting-conformant).

### KM 1.3.4 verbatim quote (QUOTE-MISSING #7 DISCHARGED, 2026-07-06T15:15Z, from
katz-mazur-arithmetic-moduli-FULL.pdf pp. 13–14 [book pp. 13–14, PDF pp. 25–26])

**Statement**: "KEY LEMMA 1.3.4. Let C/S be a smooth curve, D and D′ effective
Cartier divisors in C/S, with D′ proper over S. Then (1) there exists a unique
closed subscheme Z ⊂ S which is universal for the relation D′ ≤ D in the following
sense: given any morphism of schemes T → S, the inverse images D′_T and D_T in C_T
satisfy D′_T ≤ D_T if and only if the morphism T → S factors through Z; (2) the
subscheme Z ⊂ S is defined locally on S by deg(D′) equations; (3) formation of the
closed subscheme Z ⊂ S commutes with arbitrary change of base S′ → S, in the sense
that the closed subscheme Z′ of S′ 'universal for the relation D′_{S′} ≤ D_{S′}' is
none other than Z ×_S S′."

**Proof**: "The question is clearly local on S, which we may assume affine, say
S = Spec(R). In terms of a representative (𝔏, ℓ) for D, the condition D′ ≤ D is
that the global section ℓ of 𝔏 vanish identically in 𝔏 ⊗_{𝒪_C} 𝒪_{D′} = 𝔏|D′.
Because D′ is finite locally-free over S, and 𝔏|D′ is an invertible 𝒪_{D′}-module,
the module H⁰(D′, 𝔏|D′) is a locally free R-module of rank = deg(D′). Locally on R,
we may choose an R-basis e₁,…,e_{d′} of this R-module. The element ℓ has a unique
expression ℓ = Σᵢ rᵢeᵢ, coefficients rᵢ ∈ R. The condition 'ℓ = 0' is then
represented by the closed subscheme of Spec(R) defined by the simultaneous
vanishing of r₁,…,r_{d′}. Q.E.D."

**Lean route-deviation note (NOT B2 — statement untouched, route strictly weaker
hypotheses)**: decomposition-km1 D-inc.2's binding Lean plan already eliminates
(𝔏, ℓ); it kept a SINGLE local equation f̄ ∈ B′ (principality). Our route replaces
the single f̄ by the finitely many R-module generators of the image ideal
J := I(D)·O_{D′} (f.type: image of the lfp ideal under O_C ↠ O_{D′}, pushed to a
f.g. R-submodule of the finite R-module B′) — the vanishing locus is the span of
ALL their coordinates. Equation count k·d′ instead of d′; the Lean statement is
count-free so this is invisible; the T-D11/AG-LB/FLAT principality gates are
avoided entirely. KM 1.3.5/1.3.7 quotes also now IN CONTEXT (pp. 15–16) for T-D15/
T-D16 pickup; 1.3.7's proof confirms the three-conditions design incl. the
"(deg D)² coordinates" descent (= T-D27's lemma).

### T-D14c-1: `vanishingLocus` (Incidence.lean §VanishingLocus)

Statement: for `p : W ⟶ S` finite+flat+lfp and `E : W.IdealSheafData`, the
`S.IdealSheafData` with `ideal U := submoduleVanishingIdeal Γ(S,U) Γ(W,p⁻¹U)
(E-sections restricted)`; gluing field sorried at skeleton commit (fill next).

- Attacks: [1] **Well-definedness of the data**: needs Module Γ(S,U) Γ(W,p⁻¹U) —
  provided per-U by `letI (p.appLE …).hom.toAlgebra`; SPELLING TRAP (hit at
  skeleton build): every Γ must be at the `(affinePreimage p U).1`-spelling, not
  `p ⁻¹ᵁ U.1` — defeq but instance-synthesis-visible. [2] **Gluing (the sorried
  field)** ⟸ keystone `submoduleVanishingIdeal_localized` at S := powers f +
  the mapped-monoid instance (`isLocalizedModule_iff_isLocalization` + its
  INSTANCE at `algebraMapSubmonoid`), `Submonoid.map_powers`,
  `IsAffineOpen.isLocalization_basicOpen` both levels, `Scheme.preimage_basicOpen`
  for the open-alignment, `Submodule.localized'_eq_span` to match E's own
  `map_ideal_basicOpen`. All ingredients verified present in mathlib (session
  notes in board T-D14 progress). [3] **Junk robustness**: E arbitrary (no
  f.type needed for the DEF or gluing — only the le_ker spec's ⟸ uses
  generators); W empty / U with empty preimage: Γ(W,∅) = 0, dual of 0-module,
  submoduleVanishingIdeal = ⊥?? — over the ZERO ring Γ(W,∅)... M := 0-module:
  functional values all 0 ⟹ ideal = span{0} = ⊥ ✓ coherent (locus = all of U:
  E pulls to ⊥ on empty W vacuously ✓ matches ⊥-ideal = no condition ✓).
  SURVIVES (data + gluing plan); spec statement (T-D14c-2) gets its own block
  at statement time.


## T-D20 + T-D30 statements (beastmode-D2, 2026-07-07)

### T-D20 `flatPullback` (+ `ext`, `flatPullback_prop`, `flatPullback_ideal`, `_id`, `_flatPullback`, `baseChange_baseChange_ideal`)
Attacks:
1. **Finiteness sabotage** — bare-flat f: 𝔾ₘ ↪ 𝔸¹_{ℤₚ} (flat, NOT finite) pulls the
   proper divisor V(x²−p) back to Spec ℚₚ(√p), not finite over ℤₚ. So [IsFinite f]
   is REQUIRED for our KM-1.2.3 (proper) structure; KM p.6's bare-flat claim is for
   the propriety-free 1.1.1 notion. Hypothesis set finite+flat+lfp matches the
   structure's own fields (f contributes each by composition). DEFENDED.
2. **Orientation** — pullback ι f: condition fst ≫ ι = snd ≫ f; subscheme leg = fst,
   ambient leg = snd (closed immersion by pullback_snd). w : f ≫ π = π' (S-morphism).
   Skeleton elaborates ✓.
3. **Ideal formula truth** — ker(base-changed closed immersion) = comap needs NO
   flatness (scheme-pullback of closed subscheme = extended ideal, always):
   same 3-lemma rw as A's `baseChange_ideal` (pullbackSymmetry + ker_comp_of_isIso +
   ker_fst_of_isClosedImmersion + ker_subschemeι), f in place of (fst π t).
   KM's flatness is for INVERTIBILITY, which our working form does not carry.
4. **Instance availability for 𝟙/≫ in _id/_comp statements** — build-verified ✓
   (statements elaborate). comap_id/comap_comp existence: comap_comp ✓ (T-D14 used
   it); comap_id to probe (fallback: ext at subschemeι or map_gc).
5. **Triviality check** — composition laws are comap_id/comap_comp + `ext`; that is
   the point (API lemmas). baseChange_baseChange_ideal needs the
   pullbackLeftPullbackSndIso hom-fst compatibility simp lemma (loogle at execution).

### T-D30 `IsFullSetOfSectionsCharpoly` + `isFullSetOfSectionsAlg_iff_charpoly`
Attacks:
1. **General-endomorphism trap (T-D29's)** — form (1) MUST use `Algebra.lmul A (A⊗B) f`
   (algebra element), not an arbitrary endomorphism. Pinned ✓.
2. **n ≠ rank sabotage** — def does not force n = finrank R B. Over nontrivial A,
   either form forces n = finrank (charpoly is monic of natDegree = finrank; ∏ of n
   monic linears has natDegree n; for the norm form: at the universal/adversarial
   element the degree comparison fails likewise), and over subsingleton A both forms
   are vacuous; the iff is TRUE unconditionally. (⟸) leg: subsingleton_or_nontrivial A;
   nontrivial case derives fr = n from hyp-(1)-at-A, then sign (−1)^{fr+n} = 1.
3. **Junk-norm/junk-charpoly stratum** — [Module.Free R B] ⟹ A⊗B free over A (TC ✓
   build) — both norm and charpoly honest throughout the ∀A quantifier; the ADVERSARIAL
   FIX note on the Alg def carries over verbatim.
4. **Route for (⟹)** — hyp (2) at the R-algebra A[X] (Type u ✓) at element
   g := X ⊗ₜ 1 − (map CAlgHom id) f; `Algebra.charpoly_lmul_eq_norm A (A⊗[R]B) f`
   (T-D29, base A) + transport along e := Algebra.TensorProduct.cancelBaseChange
   R A A[X] A[X] B (EXISTS — used in NormBaseChange.lean, with cancelBaseChange_tmul /
   _symm_tmul); norm invariance under ≃ₐ: probe Algebra.norm_eq_of_algEquiv, fallback
   = norm_apply + lmul-conjugation + LinearMap.det_conj (pattern verbatim in
   NormBaseChange.lean's hconj). Factors: sectionBaseChange_tensor_map with
   ψ = Polynomial.CAlgHom (probe name; fallback: mk from C + algebraMap_eq) gives
   X − C(cᵢ) per factor; X-factor by simp [AlgHom.sectionBaseChange].
5. **(⟸) gadgets** — Algebra.norm_apply; LinearMap.det_eq_sign_charpoly_coeff;
   coeff_zero_eq_eval_zero + eval_prod/eval_sub/eval_X/eval_C; ∏(−cᵢ) = (−1)^n ∏cᵢ;
   natDegree: charpoly monic + Matrix.charpoly_natDegree route or
   LinearMap.charpoly_natDegree (probe), natDegree_prod_of_monic + natDegree_X_sub_C
   [Nontrivial A].
6. **Shadowing gotcha (hit at skeleton)** — `C` is the ambient-curve section variable
   in CartierDivisor.lean: `Polynomial.C` must be written QUALIFIED in this file.


## T-D11 statements (beastmode-D2, 2026-07-07)

### `IsOfficialCartier` (def, 2-field Prop structure)
1. KM 1.1.1 verbatim in docstring (quote-gate ✓ p. 3). Affine-local principal-nzd form;
   per-chart quotient-flatness repackaged as global subscheme flatness (Zariski-local,
   equivalent given the covering). Invertible-MODULE interface excluded → T-D19 (AG-LB).
2. ∀-points form: off-divisor points take complement charts + f = 1 (unit ideal; 1 is
   nzd) — T-D22's own case split, so the shape is consumer-proven.
3. NOT over-strong: no rank-1-freeness claim, no global principality.

### `RelEffCartierDiv.isOfficial` (KM 1.2.3 ⇐, THE MEAT)
1. Truth: KM 1.2.3 first statement verbatim (proof p. 8, transcribed in decomposition
   D-curve.2). KM route = noetherian reduction (HB-NOETH) + 1.1.5.2; OUR route is
   noetherian-FREE: (a) x ∈ D is closed in its fibre (D_s finite); fibre curve smooth
   over k(s) ⟹ O_{C_s,x} DVR ⟹ fibre ideal principal at x [RISK 1: mathlib
   smooth-over-field ⟹ DVR stalks — probe; fallback = T-D23 revival via étale-over-𝔸¹ +
   T-D22 toolkit]; (b) I fg (lfp closed immersion by cancellation vs smooth π) + lift
   fibre generator + Nakayama at O_x (m_s ⊆ m_x) + fg-support-spreading ⟹ I = (f) on a
   basicOpen [unconditional]; injectivity I⊗k(s) ↪ A⊗k(s) from S-flatness of A/I
   (Tor₁(A/I,k) = 0, KM 1.1.5.2's first-terms comparison); (c) f nzd: f̄ is fibrewise-nzd
   at EVERY point of the shrunken chart (I⊗k(s') = (f̄_{s'}) cuts the finite D_{s'} in a
   PURE-1-dim smooth fibre curve ⟹ nzd ∀ s'), then fibrewise-nzd + flat + fp ⟹ nzd =
   the SLICING CRITERION (EGA IV 11.3.7 / crit. de platitude par fibres, nzd part)
   [RISK 2 = the plan's own T-FLAT1/HB-FIBCRIT gap: probe mathlib; if absent, isolate as
   ONE private lemma and REGISTER it as the T-FLAT1 box — do not silently weaken].
   Tor-chase for (c) with J := ker(×f): J⊗k ↪ A⊗k needs Tor₁(fA,k) = 0 ⟸ Tor₂(A/f,k)=0
   — fine — but J = ker is NOT fg, so J⊗κ = 0 ∀κ does NOT give J = 0 without fp
   approximation: this is WHY (c) is genuinely the slicing lemma, not a 5-liner.
2. Adversarial: smoothness necessary? Over a nodal curve the working form contains
   non-Cartier examples (ideal of the node in a flat family) — smooth hypothesis is
   load-bearing ✓. Separatedness: probably droppable (generalise-lane note; KM ambient
   includes it — kept to match).
3. n-vs-0 degenerate: D empty near x — case handled by the off-support chart (unit
   ideal), no DVR needed there.

### `IsOfficialCartier.locallyOfFinitePresentation` / `.isFinite` / `.toRelEffCartierDiv`
1. lfp: principal ⟹ fg ideal ⟹ fp closed immersion (Algebra.FinitePresentation.quotient)
   + π lfp from hsm + composition. Plumbing-only risk (HasRingHomProperty appLE).
2. isFinite: ZMT — probe exact mathlib name (decomposition says
   `IsFinite.of_isProper_of_locallyQuasiFinite` PRESENT); locally-quasi-finite from
   fibre-finiteness of V(nzd) in a smooth affine curve over a field [RISK: dim-0 +
   finite-type ⟹ finite — if heavy, park this leg with note per claim; the def
   `toRelEffCartierDiv` then stays sorried-via-leg and is reported as such].
3. toRelEffCartierDiv: pure assembly of the three legs (one-liner fields) ✓ sorry-free
   modulo legs.
