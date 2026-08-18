# Step 4 — Mathlib API Audit: NagellLutz

**Scope.** ~55 defs + 12 abbrevs across 23 files, audited against the pinned mathlib in
`.lake/packages/mathlib` (authoritative — the local build is stale, but the **mathlib source is on
disk** and was grepped directly; this is more reliable than `loogle`/web search and needs no build).

**The single most important finding (read this first).**
This project is **not** "code that should use mathlib API" — large parts of it **are mathlib's own
elliptic-curve files, forked verbatim and extended to discharge mathlib's stated `TODO`s**, with the
goal of upstreaming. Three project files carry the **identical mathlib copyright header
("David Kurniadi Angdinata", the mathlib author)** and copy mathlib's module docstrings word-for-word:

| Project file | Is a fork of mathlib file | Relationship |
|---|---|---|
| `LutzNagell/DivisionPolynomial.lean` (80 decls, 11 defs) | `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` | **near-verbatim copy**; only changed to import the project's EDS instead of mathlib's (to avoid `normEDS`/`preNormEDS` name clashes) |
| `LutzNagell/DivisionPolynomialDegree.lean` (46 decls, 2 defs) | `Mathlib/…/DivisionPolynomial/Degree.lean` | re-proves the same degree/leading-coeff results |
| `LutzNagell/EllipticDivisibilitySequence{,Original}.lean` (161 / 138 decls) | `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` | **fork of mathlib's EDS file** (same author/docstring) **+ a large new extension layer** that proves mathlib's open `TODO`s |

Mathlib's `EllipticDivisibilitySequence.lean` docstring still says *"TODO: prove that `normEDS`
satisfies `IsEllDivSequence`"* and *"TODO: … a normalised sequence satisfying `IsEllDivSequence` can
be given by `normEDS`"*; mathlib's `DivisionPolynomial/Basic.lean` docstring still says *"TODO: the
bivariate polynomials `ωₙ`"*. **This project proves all three.** So the right framing for cleanup is
not "replace with mathlib" for the new math — it is **"these overlap mathlib exactly and should be
re-based onto it; the extension layer is the upstream contribution."**

A second structural issue: **`EllipticDivisibilitySequence.lean` and
`EllipticDivisibilitySequenceOriginal.lean` are near-duplicates of each other** (161 vs 138 decls,
same defs, same author header). One of them is dead weight. See Hand-Rolled Patterns §H1.

---

## Mathlib API Audit

### Definitions to Replace with Mathlib

These project defs are **byte-for-byte (or defeq) the mathlib definition of the same name** — mathlib
already has them with full API. The project re-declares them only because it forked the file. **Action
(global): delete the project copies and `import` mathlib; keep only the genuinely-new extension decls
(listed under "no mathlib equivalent" below).** Re-basing is the whole cleanup story here.

1. **Division-polynomial family (11 defs) → already in `Mathlib/…/DivisionPolynomial/Basic.lean`.**
   `ψ₂`, `Ψ₂Sq`, `Ψ₃`, `preΨ₄`, `preΨ'`, `preΨ`, `ΨSq`, `Ψ` (`protected`), `Φ` (`protected`),
   `ψ` (`protected`), `φ` (`protected`) — confirmed present at lines 113/117/142/147/153/194/242/290/349/401/448,
   same signatures, same namespace `WeierstrassCurve`. The project file's ~69 accompanying lemmas
   (`*_zero/one/two/three/four/even/odd/neg/ofNat`, `map_*`, `baseChange_*`, `Affine.CoordinateRing.mk_*`)
   **also all exist in mathlib's `Basic.lean`**.
   - **Action**: delete `LutzNagell/DivisionPolynomial.lean`; `import
     Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`. The only reason it was forked
     is the EDS-name clash, which disappears once the project's EDS is itself re-based on mathlib (item 3).
   - Mathlib name: `WeierstrassCurve.ψ₂`, `…Ψ₂Sq`, `…Ψ₃`, `…preΨ₄`, `…preΨ'`, `…preΨ`, `…ΨSq`,
     `…Ψ`, `…Φ`, `…ψ`, `…φ`.
   - Note: project's `Ψ₂Sq_eq` already records `W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly` (defeq to
     mathlib's `twoTorsionPolynomial`).

2. **EDS core (13 defs/recursors) → already in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.**
   `IsEllSequence` (mathlib L82), `IsDivSequence` (L87), `IsEllDivSequence` (L91), `preNormEDS'` (L124),
   `preNormEDS` (L176), `complEDS₂` (L246), `normEDS` (L289), `normEDSRec'` (L358), `normEDSRec` (L374),
   `complEDS'` (L392), `complEDS` (L427), `complEDSRec'` (L482), `complEDSRec` (L497) — **exact-name,
   exact-signature matches.** The project's `*_zero/one/two/three/four/neg/even/odd` and `map_*` lemmas
   for these also exist in mathlib.
   - **Action**: in the project EDS file, **delete these 13 and `import` mathlib's EDS file**; keep
     only the extension layer (item §"no mathlib equivalent"). This is the rebase that unblocks item 1.

3. **Degree machinery → already in `Mathlib/…/DivisionPolynomial/Degree.lean`.**
   Mathlib provides `natDegree_preΨ_le`, `coeff_preΨ`, `natDegree_preΨ`, `leadingCoeff_preΨ`,
   `natDegree_ΨSq{_le}`, `coeff_ΨSq`, `leadingCoeff_ΨSq`, `natDegree_Φ{_le}`, `coeff_Φ`,
   `leadingCoeff_Φ`, plus `natDegree_Ψ₂Sq{_le}`, `natDegree_Ψ₃`, etc. The project's
   `DivisionPolynomialDegree.lean` re-proves the same facts via the **private helpers `expDegree`
   `(n²−[4|1])/2` and `expCoeff` `if Even n then n/2 else n`**.
   - **Action**: delete `DivisionPolynomialDegree.lean` and use mathlib's Degree lemmas. mathlib does
     not expose `expDegree`/`expCoeff` by name, but its `natDegree_preΨ`/`leadingCoeff_preΨ` give the
     same closed forms — the private defs are an **implementation detail that mathlib already
     internalises**, so they carry no downstream value once mathlib's lemmas are imported.
   - Mathlib name: `WeierstrassCurve.natDegree_preΨ`, `…leadingCoeff_preΨ`, `…natDegree_Φ`, etc.

4. **Trivial curve abbreviations → use `WeierstrassCurve.baseChange` directly.**
   `LutzNagellTheorem.curveQ` (= `W.baseChange ℚ`), `PID.curveK` (= `W.baseChange K`),
   `shortCurveQ` (= `shortCurveZ.baseChange ℚ`) are one-line `abbrev`s over mathlib's
   `WeierstrassCurve.baseChange`; their `curveQ_a₁…a₆` / `curveK_a*` / `curveQ_equation_iff` lemmas
   are `rfl`/`simp` unfoldings of `baseChange`/`map`.
   - **Action**: these are acceptable local aliases (they pin the base ring for readability). **Keep**,
     but they are *not* new math — flag as zero-content wrappers. `shortCurveZ`/`cusp` are likewise
     plain `WeierstrassCurve` structure literals (no mathlib equivalent needed — they are *instances*,
     not concepts).

### Definitions with NO mathlib equivalent (the genuine contribution — keep, candidate to upstream)

Confirmed **absent** from mathlib (grepped all of `Mathlib/`; 0 hits for each name, and 0 hits for
`compl₂EDS`/`compl₂EDSAux` in `AlgebraicGeometry`/EDS — the `compl₂` hits elsewhere are unrelated
`TensorProduct`/`Induced` substrings). These fill mathlib's own `TODO`s:

- **`ω`, `ψc`, `invar`** (`DivisionPolynomialOmega.lean`) — the bivariate `ωₙ` division polynomial and
  its 2-complement. Mathlib's `Basic.lean` literally lists *"TODO: the bivariate polynomials `ωₙ`"*.
  **This is the canonical upstream target.** Built from mathlib `redInvarDenom`/`compl₂EDSAux`… which
  are themselves project-new (below). Queries: `grep '(def|abbrev) ω|ψc|compl₂EDS' Mathlib/AlgebraicGeometry/` → none.
- **EDS-is-elliptic proof layer** — `addMulSub`, `rel₄`, `net`, `Rel₃`, `Rel₄OfValid`, `relFin4`,
  `OddRec`, `EvenRec`, `HaveSameParity₄`(+`.addMulSub₄`), `StrictAnti₄`, `avg₄`, `dMin`, `cMin`,
  `rel₆`(abbrev) — Stange-net machinery reducing the 4-index elliptic relation to single-index
  recurrences. This proves mathlib's *"TODO: `normEDS` satisfies `IsEllDivSequence`"*. Queries: 0 hits each.
- **EDS complement / invariant API** — `invarNum`, `invarDenom`, `compl₂EDS`, `compl₂EDSAux`,
  `redInvarNum`, `redInvarDenom`, `EllSequence.compl'`/`compl`/`complEDS`, `universalNormEDS`,
  `Param` (inductive). Distinct from mathlib's root `complEDS` (mathlib's is `ℤ→R`; these are the
  *general* `W`-indexed complements + a "universal normalised EDS" used for the elliptic proof).
  Queries: 0 hits each.
- **Universal Weierstrass curve** (`Universal.lean`) — `Coeff` (inductive `A₁…A₆`), `curve`
  (`Affine (MvPolynomial Coeff ℤ)`), `Poly`/`Universal.Ring`/`Universal.Field`, `polyToField`,
  `specialize`, `polyEval`, `ringEval`, `pointedCurve`, `Affine.point`, `Jacobian.point`, `cusp`,
  `curvePoly`/`curveRing`/`curveField`. Mathlib's `Basic.lean` docstring *describes* this universal
  ring `ℤ[A₁,A₂,A₃,A₄,A₆][X,Y]` informally but **never constructs it as a term** — this file makes it
  concrete (the "prove on the universal curve, then specialize" device). Queries:
  `grep 'universal|MvPolynomial.*Weierstrass|specialize|inductive Coeff' Mathlib/…/EllipticCurve/` →
  only the prose docstring, no defs.
- **`n • P` coordinate maps** (`ZSMul.lean`) — `ψᵤ`, `Affine.smulX` (= `φₙ/ψₙ²`), `Affine.smulY`
  (= `ωₙ/ψₙ³`), `Affine.slopeOne`, `Jacobian.smulPoly`/`smulRing`/`smulField`, `smulEval`. These give
  the explicit division-polynomial formula for the group-law multiple `n • P`. **Mathlib has the
  group law (`Affine.Point`, `Jacobian.Point`, `dblXYZ`/`addXYZ`) but no `n•P = (φₙ:ωₙ:ψₙ)` formula**
  — grep of `Affine/Point.lean` + `Jacobian/` for `smul`/`zsmul`+`ψ`/`φ` → only `CoordinateRing` scalar
  `smul`, nothing about division polynomials. This is new and depends on `ω` (above).
- **Nagell–Lutz itself** (`LutzNagellTheorem/*`, `EvalBridge.lean`) — the theorems
  (`curveQ`/`curveK`/`shortCurveZ` denominator/discriminant/integral-multiple/prime-order results)
  and the eval bridge `evalEval_eq_of_mk_eq`. **Nagell–Lutz is not in mathlib** (grep `nagell|lutz`
  → only an unrelated author surname). The eval bridge specialises mathlib's coordinate-ring `mk`
  congruences (`Affine.CoordinateRing.mk_ψ`/`mk_φ`) to point evaluations via mathlib `evalEval` — uses
  mathlib API correctly; no equivalent needed.

### API Choice Improvements

1. **`expDegree`/`expCoeff` (private, `DivisionPolynomialDegree.lean`) → mathlib's
   `natDegree_preΨ`/`leadingCoeff_preΨ`.** Once item §Replace-3 imports mathlib's Degree file, these
   hand-rolled closed-form helpers are redundant; they exist only to *state* the degree induction that
   mathlib already carries. **Action**: drop both; consume `WeierstrassCurve.natDegree_preΨ` /
   `leadingCoeff_preΨ` / `natDegree_Φ` directly.
2. **`Int.tdiv` in `addMulSub`** (`W ((m+n).tdiv 2) * W ((m-n).tdiv 2)`) — the choice of *truncating*
   division (over `Int.ediv`/`Int.fdiv`/`/`) is deliberate ("sign-flips behave unconditionally"), and
   it has adequate mathlib API. **No change**, but note for upstreaming: mathlib EDS uses `bit`-parity
   recursion, so a reviewer may prefer the `Int.ediv` form — worth confirming with the mathlib author.
3. **`smulPoly := ![φ n, ω n, ψ n] : Fin 3 → Poly`** correctly uses mathlib's `Jacobian` `Fin 3 → R`
   point representation and `dblXYZ`/`addXYZ` formulas — **good API choice**, keep.

### Hand-Rolled Patterns to Replace

**H1. Two parallel copies of the EDS file** — `EllipticDivisibilitySequence.lean` (161 decls) and
`EllipticDivisibilitySequenceOriginal.lean` (138 decls) are the *same fork* of mathlib's EDS file with
the *same* defs and author header; `…Original` looks like the pre-extension snapshot kept alongside the
worked version. **This is duplication, not API.** **Action**: pick one (the 161-decl extended one),
delete the other, and re-base the survivor onto mathlib's `EllipticDivisibilitySequence` (§Replace-2)
so only the extension layer remains. Eliminates ~138 redundant declarations.

**H2. Forked mathlib files instead of `import` (the dominant pattern).** `DivisionPolynomial.lean` (80),
`DivisionPolynomialDegree.lean` (46), and the EDS core inside the EDS files (~25) **re-declare mathlib
verbatim**. Pattern: *fork-and-extend* where *import-and-extend* would do. **Action**: the cleanup is a
**rebase onto mathlib**, in dependency order — (a) re-base the EDS file on
`Mathlib.NumberTheory.EllipticDivisibilitySequence` keeping only `addMulSub`/`rel₄`/`net`/`compl₂EDS`/
`invar*`/`universalNormEDS`/… ; (b) delete `DivisionPolynomial.lean` + `DivisionPolynomialDegree.lean`,
`import` mathlib's `DivisionPolynomial.{Basic,Degree}`; (c) keep `Omega`/`ZSMul`/`Universal`/`LutzNagellTheorem`
as the genuine new layer on top. Net: ~150 declarations deleted, ~3 files removed, zero math lost.

**H3. `set_option allowUnsafeReducibility true` + `attribute [local reducible] Nat.rawCast …`** on
several EDS decls (`addMulSub₄`, `HaveSameParity₄.addMulSub₄`, `OddRec`, `EvenRec`, …). This is a
`norm_num`/`decide`-performance hack, not new API. **Action (for the eventual upstream PR, not blocking)**:
mathlib reviewers will want this justified or removed; flag it. Not a mathlib-replacement item.

---

## Bottom line

- **~26 of the audited defs are mathlib defs forked verbatim** (11 division-poly + 13 EDS core +
  `expDegree`/`expCoeff` standing in for mathlib Degree lemmas): **delete and import.**
- **~25 defs have no mathlib equivalent** and are the real contribution — `ω`/`ψc`/`invar`, the
  EDS-is-elliptic Stange-net layer, the universal curve, and the `n•P = (φₙ:ωₙ:ψₙ)` maps — each of
  which **discharges an explicit mathlib `TODO`** and is a strong upstream candidate.
- **~7 defs are trivial `baseChange` aliases / curve literals** (`curveQ`, `curveK`, `shortCurve*`,
  `cusp`): keep as local aliases, but they are zero math content.
- The biggest single cleanup is **structural, not API**: collapse the two EDS files into one and
  rebase the forked trio onto mathlib (~150 decls removed).
