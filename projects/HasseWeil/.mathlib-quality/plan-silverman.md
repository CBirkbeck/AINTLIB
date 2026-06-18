# Development Plan — Silverman continuation (isogenies, Tate module, formal-group bridge)

Branch: `silverman-development` (worktree `Hasse-Weil-silverman/`). Builds green (8344 jobs).
Source: Silverman, *The Arithmetic of Elliptic Curves* (2nd ed.), in-repo PDF
`HasseWeil/Silverman-Arithmetic_of_EC.pdf` (PDF page = book page + 18).
Full per-leaf, source-faithful decompositions (verbatim quotes, LOC grounded in source):
`.mathlib-quality/develop/{isogeny-foundation,tate-module,formal-group-bridge}.md`.

(The pre-existing `plan.md` / `tickets.md` / `decomposition.md` are the *completed* Hasse-bound
development — left untouched as history. This is the new continuation plan.)

## Goal

Continue the Silverman formalization on top of the (complete + cleaned) Hasse-bound work,
toward isogeny classes and, longer-term, LMFDB-style elliptic-curve labels:

1. **Faithful `Isogeny` + Silverman III.4.8.** Make the isogeny definition *faithful* (a morphism
   `φ : E₁ → E₂` with `φ(O)=O`) and **prove** that every isogeny is a group homomorphism (III.4.8)
   from the restored Pic⁰ infrastructure — so group-hom is a THEOREM, not axiomatized data.
2. **The Tate module (III.7).** `T_ℓ(E) = lim_n E[ℓⁿ] ≅ ℤ_ℓ²` (ℓ ≠ char) and the ℓ-adic Galois
   representation `ρ_ℓ : G_{K̄/K} → Aut(T_ℓ(E)) → GL₂(ℤ_ℓ)`.
3. **The formal-group ↔ isogeny bridge (IV.1.4, IV.4.3).** Close the substantive `sorry`s in
   `FormalIsogenySeries.lean` (OPTIONAL — see Workstream 3).

## Mathlib inventory

| Concept | Mathlib status | Our action |
|---|---|---|
| Weierstrass curves, `Affine.Point` group law | present | USE |
| Division polynomials (`DivisionPolynomial/{Basic,Degree}`) | present | USE |
| `ℤ_ℓ` (`PadicInt`) + `PadicInt.lift` (proj-limit universal property), `toZModPow`, `ext_of_toZModPow` | present | USE — load-bearing for the Tate module |
| `Ideal.ramificationIdx`/`inertiaDeg`, `Ideal.sum_ramification_inertia`, `Algebra.norm` | present | USE — for `h_pres` (norm–conorm) |
| `GL (Fin 2)`, `Matrix.GeneralLinearGroup`, `LinearMap.toMatrix` | present | USE — for ρ_ℓ in GL₂ form |
| EC isogeny abstraction, Pic⁰ / divisor theory for EC | in project (not mathlib) | USE project code |
| Formal groups | in project, sorry-free | USE read-only |
| Tate module, generic inverse limit of a module tower | NOT in mathlib | NEW (hand-build) |

## Workstream 1 — Faithful Isogeny + III.4.8 (PRIORITY; smallest real gap)

**Correct definition (III.4, p.66, verbatim):** *"An isogeny from E₁ to E₂ is a morphism
φ : E₁ → E₂ satisfying φ(O) = O"* (zero isogeny included; `deg[0]=0`). Group-hom is **III.4.8**
(p.71), proved via the divisor pushforward `φ_*` on Pic⁰ and the Abel–Jacobi iso `κ : E ≅ Pic⁰(E)`
(III.3.4). Both current structures are non-faithful: `Basic.Isogeny` carries `toAddMonoidHom` as
*data* (axiomatized group hom); `EC.Isogeny` (CurveMap-based, the faithful carrier) leaves group-hom
as the unproven `Prop AddHomProperty`.

**III.4.8 spine (mirror of Silverman p.71):**
```
φ ≡ O → trivial
φ finite → φ_* : Pic⁰(E₁)→Pic⁰(E₂) group hom         [LEAF4 = the only gap]
          κᵢ : Eᵢ ≅ Pic⁰(Eᵢ) group iso (III.3.4)      [DONE: picZeroIsoE_allChar]
          square κ₂∘φ = φ_*∘κ₁ (φ(O)=O)               [DONE: picZeroOfPoint_pushforwardPicZero]
          chase: κ₂ inj + homs ⟹ φ hom                [DONE: AddHomProperty_of_picZero_witnesses]
```

**The single gap — LEAF4 `h_pres`:** `φ_*` sends principal divisors to principal, via the
norm–conorm identity `div(N_φ f) = φ_*(div f)` (Silverman II.3.6). **Trap:** the σ-criterion route
is *circular* (it presupposes `Σ ord_P(f)·φP = φ(Σ ord_P(f)·P)` = φ being a hom). Must go via the
norm conorm (`CurveMap.pushforward` = `Algebra.norm`, already defined). Degree side already in
`NormValuation.lean`; the full divisor identity is new. ~250–450 LOC.

**Design decision (DECIDE at approval):** state III.4.8 primarily at the **divisor/σ level** — it then
holds for *all* isogenies including `[n]` (n≥2) and `1−π`, which have **no affine `CoordHom`** (their
x-image has poles at torsion) so the point-map form is vacuous for them. Derive the point-map
`AddHomProperty cd` corollary only where a `CoordHom` exists (e.g. Frobenius). More faithful, and what
downstream (the dual isogeny) needs.

**Dependency graph.** `[DONE LEAF1,2,3] → LEAF4 (h_pres, norm conorm) → LEAF6 (package AddHomProperty
over IsAlgClosed) → LEAF7 (descend to K via base-change)`. `LEAF0` (minimal `EC.Isogeny→Basic.Isogeny`
bridge) early; full migration deferred as cleanup. ~300–550 LOC total. Detail:
`develop/isogeny-foundation.md`.

## Workstream 2 — The Tate module T_ℓ(E) ≅ ℤ_ℓ² + ℓ-adic representation (III.7)

Greenfield (no Tate code in project or mathlib). Builds on the existing `E[ℓ]≅(ℤ/ℓ)²` stack.

- **Phase 1 — `E[ℓⁿ]≅(ℤ/ℓⁿ)²`.** L1 `(ℓⁿ:F)≠0`; L2 `#E[ℓⁿ]=ℓ^{2n}` (instantiate the *general-ℤ*
  `card_torsion_ell` at `ℓⁿ`); L3 `ZMod(ℓⁿ)`-module on `E[ℓⁿ]`; **L4** `E[ℓⁿ]≅(ZMod ℓⁿ)²` — hard new
  math (over a *non-field* cardinality doesn't pin the module; coherent induction lifting bases along
  `[ℓ]`). ~120–180 LOC, ≈30–50% of the topic.
- **Phase 2 — inverse system.** L5 connecting `[ℓ]:E[ℓⁿ⁺¹]→E[ℓⁿ]`; L6 `ZMod`-semilinearity along
  `ZMod.castHom`; L7 surjectivity (optional — topology remark only).
- **Phase 3 — `T_ℓ ≅ ℤ_ℓ²`.** L8 hand-built `AddSubgroup` of `Π E[ℓⁿ]` with a `ℤ_ℓ`-action through
  `PadicInt.toZModPow` (no mathlib generic limit); **L9** `lim ZMod(ℓⁿ)≅ℤ_ℓ` via `PadicInt.lift`
  (low-risk mathlib win); L10 assembly `T_ℓ≅ℤ_ℓ²` (naturality — couples to L4's coherent bases).
- **Phase 4 — ρ_ℓ.** L11 Galois action on `E[ℓⁿ]` (`Affine.Point.map σ`); L12 commutes with `[ℓ]`,
  assembles `rhoTate`; L13 `ρ_ℓ` group hom; L14 GL₂ form (optional); **L15 continuity — OUT OF SCOPE**.
- **Out of scope:** Thm 7.4 / Cor 7.5 (`Hom⊗ℤ_ℓ ↪ Hom(T_ℓ)`), continuity. ~700–950 LOC. Detail:
  `develop/tate-module.md`.

## Workstream 3 — Formal-group ↔ isogeny bridge (IV.1.4, IV.4.3) — OPTIONAL

**The two `FormalIsogenySeries.lean` sorries are NOT load-bearing:** the Hasse bound (axiom-clean) gets
its `omegaPullbackCoeff` facts from `RouteBInduction` (III.5.2/5.3, sorry-free), and the abstract
IV.4.3 (`FormalGroupHom.invariantDifferential_chain`) + all of `FormalGroup/` are sorry-free. No
external consumer of the bare sorries.
- **Track A (BRIDGE-001, IV.4.3 general):** build `curveFormalGroup` + `isogFormalHom` + a
  `localExpand`-differential bridge, invoke the proven abstract chain rule. A0 `assoc` (~250–500), A2
  (~300–600). *Already closed for every relevant isogeny* via composition.
- **Track B (BRIDGE-003, IV.1.4 general):** B2 = `localExpand(addPullback)=subst[f_α,f_β] F̂`, the
  irreducible hard core (~600–1200 LOC). **B2 also unblocks the V-side pole bound** — its real value.
- **Track C (EDS Wronskian):** OUT OF SCOPE — needs a new mathlib Ward-addition-formula API; bypassed.

**Recommendation:** defer; or restate the two general sorries witness-parametrically (wrappers exist)
and delete the bare sorries. Detail: `develop/formal-group-bridge.md`.

## LMFDB / elliptic-curve-labels roadmap (honest scope)

- **Reachable from this plan:** the faithful isogeny + III.4.8 gives a well-defined **isogeny class**
  ("∃ isogeny E₁→E₂"; III.6.1 makes it symmetric via the dual) — this *is* LMFDB's isogeny-class
  notion. Buildable once Workstream 1 lands.
- **The large gap:** LMFDB EC labels are `[conductor].[isogeny-class].[curve#]` over **ℚ**. The
  **conductor** needs bad-reduction analysis — Néron models / Tate's algorithm (Silverman Ch VII + App
  C §15) — which mathlib does **not** have, and the project is currently general-field / 𝔽_q. Full
  LMFDB labelling is a **major separate arithmetic-over-ℚ program**, beyond this plan. The isogeny +
  isogeny-class layer is the foundation to lay first.

## Generality decisions

- Isogeny over general `[Field F]`; III.4.8 over `[IsAlgClosed F]` (geometric), then descended to `K`.
  Keep `EC.Isogeny` (CurveMap-based) as the faithful carrier.
- Tate module: `K` finite, `F = AlgebraicClosure K`; ℓ-adic objects over `ℤ_[ℓ]` / `ZMod (ℓ^n)`; state
  at max generality the per-`n` ring `ZMod(ℓⁿ)` allows (not a field).
- Prefer divisor/σ-level statements (CoordHom-free) so results cover `[n]`/`1−π`.

## Recommended sequencing

1. **Workstream 1** (foundational, smallest gap, directly answers the isogeny question). LEAF4
   (`h_pres`) is the whole job; LEAF1–3 are citations; LEAF6/7 wiring.
2. **Workstream 2** (Tate module — greenfield, explicitly requested; L4 + L8/L10 carry the risk).
3. **Workstream 3** (optional; only B2 has downstream value).

`/develop` is planning-only. After approval, `/beastmode` works the tickets in `tickets-silverman.md`.
