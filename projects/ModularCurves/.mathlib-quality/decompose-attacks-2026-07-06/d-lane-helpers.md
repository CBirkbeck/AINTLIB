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
