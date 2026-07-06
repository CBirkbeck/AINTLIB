# Adversarial attack blocks — D-lane Wave-0 helper declarations (beastmode-D2)

New helper statements get their block here at statement time (v5 rule; standing
rule 1). Format mirrors `level-structures.md`.

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
