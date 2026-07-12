# Inventory: `projects/ModularCurves/ModularCurves/Moduli/NaiveProblems.lean`

Phase-1 /overview inventory (y1 pass). File: 243 lines, module `ModularCurves.Moduli.NaiveProblems`.
Relocation home (v10.117 doctrine) of the naive level-structure moduli problems + held theorems,
moved byte-identical out of `Moduli/Representability.lean` so the parked sorries can consume
`PullSectionCanonicity.lean`.

**Imports**: `ModularCurves.Moduli.Representability`, `ModularCurves.Moduli.PullSectionCanonicity`,
`ModularCurves.EllipticCurve.TorsionFibre`.
**Namespace**: everything in `namespace ModularCurves`, `section LevelModuli`,
`variable (R : CommRingCat.{u})`. **Imported by** (out-of-file context): `ModularCurve/YOneAssembly.lean`,
`ModularCurve/YFullRoute.lean`, `Moduli/GammaH.lean`, `Moduli/Groupoid.lean`, `Moduli/Bootstrap.lean`,
`Moduli/GammaHRepresentability.lean`.

---

## 1. `ModularCurves.EllHom.pullSection_add`

- **Type**: theorem
- **What**: (T-E4a) Section-pullback along an `Ell/R`-morphism is additive:
  `pullSection R f (P + Q) = pullSection R f P + pullSection R f Q` for `f : X ⟶ Y` in `Ell/R`
  and `P Q : Y.curve.Section`. Not free: `EllHom` carries no group-compatibility field; the
  content is GME Cor 2.2.5 (a pointed iso onto the pullback is automatically a group iso).
- **How**: one-line term-mode delegation to `EllHom.pullSection_add_of_finitePresentation`
  (the finite-presentation transport proved in `Moduli/PullSectionCanonicity.lean:177`).
- **Hypotheses**: `R : CommRingCat.{u}` (section var); `X Y : EllObj R`; `f : X ⟶ Y`;
  `P Q : Y.curve.Section`.
- **Uses from project**: `EllObj`, `EllHom` + its category structure (`Moduli/EllCategory.lean`);
  `EllipticCurve.Section` (`LevelStructure/ExactOrder.lean:46`) with its `AddCommGroup` instance
  (`EllipticCurve/GroupLaw.lean`); `EllHom.pullSection` (`Moduli/Representability.lean:148`);
  `EllHom.pullSection_add_of_finitePresentation` (`Moduli/PullSectionCanonicity.lean:177`).
- **Used by (in file)**: [] — mentioned in the docstring of `isNaiveGammaOne_pullSection_iff`
  but never called by in-file code.
- **Visibility**: public
- **Lines**: 35–39 (docstring 27–34); proof 1 line
- **Notes**: sorry-free (previously one of the "parked sorries" of the header — now discharged).
  Docstring claims "Every moduli-functor `map` below … consumes this lemma"; literally, no in-file
  `map` calls it (the Γ₁ map goes through the `_of_finitePresentation` siblings via the iff-lemmas;
  Γ(N)/P_H/Drinfeld maps are elsewhere or sorried) — stale/relocation-scoped docstring claim.

## 2. `ModularCurves.pull_transportSection_eq_zero_iff`

- **Type**: lemma (private)
- **What**: (Y1-D2 bridge) For `f : X ⟶ Y` in `Ell/R`, a field `k`, a geometric point
  `τ : Spec k ⟶ X.base` and `w : X.curve.Section`: the pulled point `Point.pull X.curve τ w`
  vanishes iff the pulled point of its `transportSection` (on the base-changed curve
  `Y.curve.baseChange f.baseHom`) vanishes. The "barehanded" fibrewise transport of the
  wiring note.
- **How** (proof 12 lines, >10): pure iso-cancellation on total spaces. Rewrites both sides to
  compositions with `(EllHom.curveIsoPullback R f).hom` (`key` via `Category.assoc`; `keyzero` via
  `EllipticCurve.point_zero_val` twice + `EllHom.zero_curveIsoPullback`), then closes with
  `CategoryTheory.cancel_mono` applied to the iso's hom (iso ⟹ mono).
- **Hypotheses**: `R : CommRingCat.{u}`; `X Y : EllObj R`; `f : X ⟶ Y`; `k : Type u` `[Field k]`;
  `τ : Spec (CommRingCat.of k) ⟶ X.base`; `w : X.curve.Section`.
- **Uses from project**: `EllipticCurve.Point.pull` (`LevelStructure/ExactOrder.lean:49`);
  `EllipticCurve.baseChange` (`EllipticCurve/GroupLaw.lean:152`); `EllHom.transportSection`
  (`Moduli/PullSectionAdd.lean:60`); `EllHom.curveIsoPullback` (`Moduli/PullSectionAdd.lean:40`);
  `EllHom.zero_curveIsoPullback` (`Moduli/PullSectionAdd.lean:44`); `EllipticCurve.point_zero_val`
  (`EllipticCurve/TorsionFibre.lean:254`); `EllHom.baseHom` field (`Moduli/EllCategory.lean`).
- **Used by (in file)**: `isNaiveGammaOne_pullSection_iff` (line 103).
- **Visibility**: private
- **Lines**: 45–60 (docstring 41–44)
- **Notes**: sorry-free.

## 3. `ModularCurves.isNaiveGammaOne_pullSection_iff`

- **Type**: theorem
- **What**: (Y1-D2, naive-structure transport) For `f : X ⟶ Y` in `Ell/R` and
  `Q : Y.curve.Section`: `pullSection f Q` is naive-`Γ₁(N)` on `X.curve` **iff** the pulled
  *point* (as a section of the base-changed curve `Y.curve ×_{Y.base} X.base` via `asSection`)
  is naive-`Γ₁(N)`. The two-sided dictionary between section-level and base-change-level naive
  level structure.
- **How** (proof ~42 lines, >30): transports the two clauses of `IsNaiveGammaOne` through the
  injective additive hom `Φ := AddMonoidHom.mk' (transportSection R f)
  (transportSection_add_of_finitePresentation R f)` (injectivity:
  `EllHom.transportSection_injective`). The killing clause `(N : ℤ) • _ = 0` transfers by
  `map_zsmul Φ` + the dictionary `hdict` (`EllHom.transportSection_pullSection`: transport of the
  pulled section IS the base-changed pulled point-section, up to `Subtype.ext`/`rfl`). The
  fibrewise exact-order clause transfers by `hbridge`: for every `a : ℤ` and geometric point `t`,
  `EllipticCurve.Point.pull_zsmul` pushes the scalar inside and the private
  `pull_transportSection_eq_zero_iff` iso-cancels; both directions of the iff then destructure
  `⟨hkill, hfib⟩` and reassemble with `not_congr` on the order clause.
- **Hypotheses**: `R : CommRingCat.{u}`; `N : ℕ` `[NeZero N]`; `X Y : EllObj R`; `f : X ⟶ Y`;
  `Q : Y.curve.Section`.
- **Uses from project**: `EllipticCurve.IsNaiveGammaOne` (`LevelStructure/Basic.lean:62`);
  `EllHom.pullSection` (`Moduli/Representability.lean:148`); `EllHom.transportSection`,
  `EllHom.transportSection_injective`, `EllHom.transportSection_pullSection`
  (`Moduli/PullSectionAdd.lean:60/66/74`); `EllHom.transportSection_add_of_finitePresentation`
  (`Moduli/PullSectionCanonicity.lean:153`); `EllipticCurve.Point.asSection`
  (`EllipticCurve/GroupLaw.lean:237`); `EllipticCurve.Point.pull`, `EllipticCurve.Point.pull_zsmul`
  (`LevelStructure/ExactOrder.lean:49/54`); `EllipticCurve.baseChange`
  (`EllipticCurve/GroupLaw.lean:152`); in-file private `pull_transportSection_eq_zero_iff`.
- **Used by (in file)**: `gammaOneNaiveProblem` (`map` field, line 195).
- **Visibility**: public
- **Lines**: 70–117 (docstring 62–69) — **proof >30 lines**
- **Notes**: sorry-free. Docstring is a relocation relic: it still speaks of "the membership sorry
  inside `gammaOneNaiveProblem.map` (held file)" — that sorry is now discharged by this very
  lemma at lines 195–196, and the file is no longer "held" in that sense. Docstring's
  "prove once, consume twice" coordination note is now realised.

## 4. `ModularCurves.baseChangeEquiv_pull_asSection`

- **Type**: lemma (private)
- **What**: the `baseChangeEquiv`-dictionary at geometric points: base-changed pull of
  `asSection` equals pull along the composite, i.e.
  `baseChangeEquiv Y.curve f.baseHom t (pull (baseChange) t (asSection (pull Y.curve f.baseHom Q)))
  = pull Y.curve (t ≫ f.baseHom) Q`.
- **How** (proof 6 lines): `Subtype.ext`, unfold via
  `EllipticCurve.Point.baseChangeEquiv_apply_coe`, reassociate (`Category.assoc`), collapse the
  first pullback projection with `EllipticCurve.Point.asSection_val_fst`, finish by `rfl`.
- **Hypotheses**: `R : CommRingCat.{u}`; `X Y : EllObj R`; `f : X ⟶ Y`; `T : Scheme.{u}`;
  `t : T ⟶ X.base`; `Q : Y.curve.Section`.
- **Uses from project**: `EllipticCurve.Point.baseChangeEquiv`,
  `EllipticCurve.Point.baseChangeEquiv_apply_coe`, `EllipticCurve.Point.asSection`,
  `EllipticCurve.Point.asSection_val_fst` (all `EllipticCurve/GroupLaw.lean:392/404/237/248`);
  `EllipticCurve.Point.pull` (`LevelStructure/ExactOrder.lean:49`); `EllipticCurve.baseChange`
  (`EllipticCurve/GroupLaw.lean:152`).
- **Used by (in file)**: `isNaiveGammaOne_asSection_pull` (lines 181, 185).
- **Visibility**: private
- **Lines**: 121–133 (docstring 119–120)
- **Notes**: sorry-free.

## 5. `ModularCurves.isNaiveGammaOne_asSection_pull`

- **Type**: lemma (private)
- **What**: naive `Γ₁(N)` structures transport to the base change along an `Ell/R`-morphism's
  base: if `Q` is naive-`Γ₁(N)` on `Y.curve` then
  `asSection Y.curve f.baseHom (pull Y.curve f.baseHom Q)` is naive-`Γ₁(N)` on
  `Y.curve.baseChange f.baseHom`. Supplies the target-side input of
  `isNaiveGammaOne_pullSection_iff`.
- **How** (proof ~46 lines, >30): destructures `hQ` into the killing and fibrewise clauses.
  Killing clause: pushes `(N : ℤ) •` through `EllipticCurve.Point.asSection_zsmul` and
  `EllipticCurve.Point.pull_zsmul`, rewrites by `hkill` and `EllipticCurve.Point.pull_zero`, then
  proves the two zero-sections equal by `Limits.pullback.hom_ext` with per-projection
  computations (`EllipticCurve.Point.asSection_val_fst`/`asSection_val_snd`,
  `point_zero_val`, `Limits.pullback.lift_fst`/`lift_snd`, `Category.id_comp`). Fibrewise clause:
  for each field-point `t`, conjugates through the additive equiv
  `EllipticCurve.Point.baseChangeEquiv` (`hbc`: `map_zsmul`/`map_zero` + the private
  `baseChangeEquiv_pull_asSection`, injectivity of the equiv for the converse), then re-indexes
  the source clause at the composite point `t ≫ f.baseHom`.
- **Hypotheses**: `R : CommRingCat.{u}`; `N : ℕ` `[NeZero N]`; `X Y : EllObj R`; `f : X ⟶ Y`;
  `Q : Y.curve.Section`; `hQ : Y.curve.IsNaiveGammaOne N Q`.
- **Uses from project**: `EllipticCurve.IsNaiveGammaOne` (`LevelStructure/Basic.lean:62`);
  `EllipticCurve.Point.asSection`, `asSection_zsmul`, `asSection_val_fst`, `asSection_val_snd`,
  `baseChangeEquiv` (all `EllipticCurve/GroupLaw.lean:237/268/248/253/392`);
  `EllipticCurve.Point.pull`, `pull_zsmul`, `pull_zero` (`LevelStructure/ExactOrder.lean:49/54/83`);
  `EllipticCurve.point_zero_val` (`EllipticCurve/TorsionFibre.lean:254`); `EllipticCurve.baseChange`
  (`EllipticCurve/GroupLaw.lean:152`); `EllipticCurve.π` / `zero` fields; in-file private
  `baseChangeEquiv_pull_asSection`.
- **Used by (in file)**: `gammaOneNaiveProblem` (`map` field, line 196).
- **Visibility**: private
- **Lines**: 137–187 (docstring 135–136) — **proof >30 lines**
- **Notes**: sorry-free. The killing-clause branch (lines 144–170) has a convoluted `hL` chain at
  148–154 (`.trans … ▸ ….trans` with a `rfl`-congrArg) — a golf candidate once the file leaves
  producer hands.

## 6. `ModularCurves.gammaOneNaiveProblem`

- **Type**: noncomputable def
- **What**: the naive `Γ₁(N)` moduli problem over `R` as a `ModuliProblem R`
  (= presheaf `(EllObj R)ᵒᵖ ⥤ Type u`): `E/S ↦ {P ∈ E(S) : P has naive exact order N}`
  (fibrewise; right notion for `N` invertible, KM 1.4.4; Loeffler §3.3/§3.8, KM 3.2 + 3.7).
  `map` pulls the section back and transports membership.
- **How**: functor-of-points construction. `obj` is the subtype over `IsNaiveGammaOne N`;
  `map f` is `↾fun P => ⟨pullSection f.unop P.1, …⟩` with membership discharged by
  `(isNaiveGammaOne_pullSection_iff …).mpr (isNaiveGammaOne_asSection_pull …)`;
  `map_id`/`map_comp` reduce to `EllHom.pullSection_id` / `EllHom.pullSection_comp` after
  `ext` + `congrArg Subtype.val`.
- **Hypotheses**: `R : CommRingCat.{u}`; `N : ℕ` `[NeZero N]`.
- **Uses from project**: `ModuliProblem` (`Moduli/EllCategory.lean:91`); `EllObj`, `EllHom`
  (`Moduli/EllCategory.lean:38/59`); `EllipticCurve.IsNaiveGammaOne`
  (`LevelStructure/Basic.lean:62`); `EllHom.pullSection`, `EllHom.pullSection_id`,
  `EllHom.pullSection_comp` (`Moduli/Representability.lean:148/155/168`); in-file
  `isNaiveGammaOne_pullSection_iff` and private `isNaiveGammaOne_asSection_pull`.
- **Used by (in file)**: [] — the T-E7 MASTER `gammaOneNaive_representable` that consumed it was
  relocated to `ModularCurve/YOneTatePoint.lean` (see relic comment, lines 221–224). Heavily
  consumed out-of-file (YOneTatePoint/YOneAssembly/GammaH/Groupoid/Bootstrap chain).
- **Visibility**: public
- **Lines**: 192–202 (docstring 189–191)
- **Notes**: sorry-free — the former "membership sorry inside `gammaOneNaiveProblem.map`" is
  discharged. Docstring line "Functor laws are `T-E4`" is ticket-tag prose.

## 7. `ModularCurves.gammaFullNaiveProblem`

- **Type**: noncomputable def
- **What**: the naive full-level-`N` (`Γ(N)`) moduli problem over `R`:
  `E/S ↦ {(P, Q) : pairs of sections generating E[N] in every fibre}` (Loeffler Fact 3.8.1
  verbatim; KM 3.1 + 3.7), as a `ModuliProblem R`. `map` pulls both sections back.
- **How**: same functor-of-points shape as `gammaOneNaiveProblem`: `obj` is the subtype of
  `Section × Section` over `IsNaiveFullLevel N`; `map f` pulls componentwise via
  `EllHom.pullSection` — **membership proof is `by sorry`**; `map_id`/`map_comp` close
  componentwise by `EllHom.pullSection_id` / `EllHom.pullSection_comp` after `ext` +
  `congrArg Subtype.val`.
- **Hypotheses**: `R : CommRingCat.{u}`; `N : ℕ` `[NeZero N]`.
- **Uses from project**: `ModuliProblem`, `EllObj`, `EllHom` (`Moduli/EllCategory.lean`);
  `EllipticCurve.IsNaiveFullLevel` (`LevelStructure/Basic.lean:45`); `EllHom.pullSection`,
  `EllHom.pullSection_id`, `EllHom.pullSection_comp` (`Moduli/Representability.lean:148/155/168`).
- **Used by (in file)**: `gammaFullNaive_representable` (statement, lines 236–238).
- **Visibility**: public
- **Lines**: 207–219 (docstring 204–206)
- **Notes**: **CODE-sorry** — actual `sorry` TERM at line 211, inside the `map` field: the
  obligation is `IsNaiveFullLevel N (pullSection f PQ.1.1) (pullSection f PQ.1.2)` (full-level
  membership transport along pullSection — the Γ(N) analogue of the discharged Γ₁ membership;
  per the header wiring note it awaits the killing-clause transport
  `pullSection_zsmul_of_finitePresentation` + fibrewise `Point.pull`-compatibility).
  Producer-WIP, cleanup-untouchable.

## 8. (comment block, lines 221–224 — not a declaration)

- **What**: RELOCATED pointer (Y1-CLOSER S6, v10.111/117 doctrine): the held T-E7 MASTER
  `gammaOneNaive_representable` now lives byte-identical in `ModularCurve/YOneTatePoint.lean`,
  closed there by `gammaOneNaive_representable_assembly` (zero code-consumers of the name at
  relocation time — the cap theorem).
- **Notes**: relocation-relic pointer comment, intentional per doctrine; keep until the board
  retires the pointer.

## 9. `ModularCurves.gammaFullNaive_representable`

- **Type**: theorem
- **What**: (T-E9 = Loeffler Prop 3.8.2–3.8.3; KM 3.1/4.7/5.1) For `N ≥ 3` and `N` invertible
  in `R`: `[Γ(N)]` (i.e. `gammaFullNaiveProblem R N`) is rigid and representable, AND any
  representing object `X` has `Smooth X.structMap ∧ IsAffineHom X.structMap` (the representing
  scheme `Y(N)` is smooth and affine over `Spec R`; smooth+affine conjunct restored 2026-07-06
  after being in the docstring but missing from the statement).
- **How**: `by sorry` — no proof.
- **Hypotheses**: `R : CommRingCat.{u}`; `N : ℕ` `[NeZero N]`; `hN : 3 ≤ N`;
  `hinv : IsUnit (N : R)`.
- **Uses from project** (statement): in-file `gammaFullNaiveProblem`; `ModuliProblem.Rigid`
  (`Moduli/EllCategory.lean:168`); `ModuliProblem.Representable` (abbrev over mathlib
  `Functor.IsRepresentable`, `Moduli/EllCategory.lean:149`); `EllObj` + `EllObj.structMap` field
  (`Moduli/EllCategory.lean:38`). (`.RepresentableBy` is mathlib
  `CategoryTheory.Functor.RepresentableBy`; `Smooth`/`IsAffineHom` are mathlib
  `AlgebraicGeometry` classes.)
- **Used by (in file)**: []
- **Visibility**: public
- **Lines**: 234–239 (docstring 226–233)
- **Notes**: **CODE-sorry** — the entire proof is the `sorry` term at line 239. Producer-WIP
  (T-E9), cleanup-untouchable. Docstring records the rigidity source-of-record split
  (Loeffler 3.8.3 for `Ell/R[1/6]`; GME 2.6.4 chain B9 for residue chars 2,3; "KM locator
  pending").

---

### File Summary

- **Total declarations**: 8 (3 theorems, 3 lemmas, 2 noncomputable defs) + 1 relocation pointer
  comment block (lines 221–224). All inside `namespace ModularCurves`, section `LevelModuli`,
  `variable (R : CommRingCat.{u})`.
- **Key API (3+ in-file users)**: none — the in-file dependency graph is a chain (each helper has
  exactly one in-file consumer). The file's real API surface is downstream:
  `gammaOneNaiveProblem` / `gammaFullNaiveProblem` are consumed by the 6 importing modules
  (YOneAssembly, YFullRoute, GammaH, Groupoid, Bootstrap, GammaHRepresentability; the relocated
  T-E7 MASTER in YOneTatePoint).
- **Unused-in-file**: `EllHom.pullSection_add` (docstring-mentioned only),
  `gammaOneNaiveProblem` (consumers relocated out per v10.111/117), `gammaFullNaive_representable`.
- **CODE-sorry list (exact carriers)**: 2 —
  1. `ModularCurves.gammaFullNaiveProblem` — `sorry` term at line 211 inside the `map` field
     (the `IsNaiveFullLevel` membership transport for the pulled pair);
  2. `ModularCurves.gammaFullNaive_representable` — proof is `by sorry` (line 239, T-E9).
  Both producer-WIP, cleanup-untouchable. (Header prose also *mentions* "three parked sorrys" —
  that is docstring prose, not code; only the two above are code.)
- **set_option**: none.
- **Proofs >30 lines**: `isNaiveGammaOne_pullSection_iff` (~42 proof lines, lines 70–117);
  `isNaiveGammaOne_asSection_pull` (~46 proof lines, lines 137–187).
- **private/public**: 3 private (`pull_transportSection_eq_zero_iff`,
  `baseChangeEquiv_pull_asSection`, `isNaiveGammaOne_asSection_pull`) / 5 public
  (`EllHom.pullSection_add`, `isNaiveGammaOne_pullSection_iff`, `gammaOneNaiveProblem`,
  `gammaFullNaiveProblem`, `gammaFullNaive_representable`).
- **Relocation relics / stale docstrings**:
  1. Module header (lines 5–15) still says "the three parked `sorry`s" — only 2 code-sorries
     remain (`pullSection_add` and the Γ₁ membership were since discharged); partially stale.
  2. `isNaiveGammaOne_pullSection_iff` docstring (lines 62–69) refers to "the membership sorry
     inside `gammaOneNaiveProblem.map` (held file)" — that sorry is now discharged by this very
     lemma (lines 195–196); stale.
  3. Lines 221–224: explicit RELOCATED pointer for `gammaOneNaive_representable` →
     `ModularCurve/YOneTatePoint.lean` (intentional doctrine pointer, keep).
  4. `EllHom.pullSection_add` docstring (lines 27–34) claims "Every moduli-functor `map` below …
     consumes this lemma" — no in-file `map` code-consumes it (the Γ₁ map consumes the
     `_of_finitePresentation` siblings via the iff-lemmas); scoped-to-old-file claim, stale.
