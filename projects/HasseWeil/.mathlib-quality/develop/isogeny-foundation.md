# Faithful Isogeny + Silverman III.4.8 (group-hom via Pic⁰) — source-faithful decomposition

Topic owner scope: (1) consolidate the two `Isogeny` structures into ONE faithful
definition (morphism / `CurveMap` with strict `φ(O)=O`), and (2) PROVE Silverman
III.4.8 (every isogeny is a group homomorphism) from the now-restored Pic⁰
infrastructure, so that group-hom becomes a THEOREM, not axiomatized data.

Verified against the in-repo PDF
`Hasse-Weil-silverman/HasseWeil/Silverman-Arithmetic_of_EC.pdf`
(book page = PDF page − 18). All page refs below are BOOK pages.

---

## (a) The source's correct definitions and statements (faithful, with quotes)

### A.1 Definition of isogeny (III.4, book p.66)

> **Definition.** Let `E₁` and `E₂` be elliptic curves. An *isogeny* from `E₁` to
> `E₂` is a morphism `φ : E₁ ⟶ E₂` satisfying `φ(O) = O`.

> It follows from (II.2.3) that an isogeny satisfies either `φ(E₁) = {O}` or
> `φ(E₁) = E₂`. Thus except for the zero isogeny defined by `[0](P) = O` …, every
> other isogeny is a finite map of curves. Hence we obtain the usual injection of
> function fields, `φ* : K̄(E₂) ⟶ K̄(E₁)`.

So: the **zero isogeny `[0]` IS an isogeny by convention** (`φ(E₁)={O}`); every
*nonzero* isogeny is finite and induces the function-field pullback `φ*`. The
degree is `deg φ = [K̄(E₁) : φ*K̄(E₂)]`, with `deg[0] = 0` by convention (p.66).

### A.2 `Hom(E₁,E₂)` and `End(E)` (III.4, book p.67)

> The sum of two isogenies is defined by `(φ + ψ)(P) = φ(P) + ψ(P)`, and (III.3.6)
> implies that `φ+ψ` is a morphism, so it is an isogeny. Hence `Hom(E₁,E₂)` … is a
> group.

Key: `+` on `Hom` is *defined pointwise via the group law on `E₂`* and is a
morphism *because addition `E₂×E₂→E₂` is a morphism* (III.3.6). The
*distributivity* `(φψ)+(φψ')=φ(ψ+ψ')` is NOT obvious and is deferred (it follows
from III.4.8 — Silverman flags this explicitly, p.67).

### A.3 Every morphism = translation ∘ isogeny (Example 4.7, book p.71)

> Now consider an arbitrary morphism `F : E₁ ⟶ E₂` of elliptic curves. The
> composition `φ = τ_{−F(O)} ∘ F` is an isogeny, since `φ(O) = O`. This proves that
> any morphism `F` between elliptic curves can be written as `F = τ_{F(O)} ∘ φ`.

### A.4 **Theorem III.4.8** (the target, book p.71)

> **Theorem 4.8.** Let `φ : E₁ ⟶ E₂` be an isogeny. Then `φ(P+Q) = φ(P) + φ(Q)`
> for all `P,Q ∈ E₁`.

### A.5 The Abel–Jacobi correspondence used in the proof (III.3.4, book p.61–63)

> **Proposition 3.4.** Let `(E,O)` be an elliptic curve.
> (a) For every degree-0 divisor `D ∈ Div⁰(E)` there exists a unique point `P ∈ E`
>     satisfying `D ∼ (P) − (O)`. Define `σ : Div⁰(E) ⟶ E` … sending `D` to its
>     associated `P`.
> (c) … `σ` induces a bijection of sets … `σ : Pic⁰(E) ⥲ E`.
> (d) The inverse to `σ` is the map `κ : E ⥲ Pic⁰(E)`, `P ↦ (divisor class of
>     (P) − (O))`.

> `κ(P+Q) = κ(P) + κ(Q)` … This proves that `κ is a group homomorphism`. (p.63)

So both `σ` and `κ = σ⁻¹` are **group isomorphisms** `Pic⁰(E) ≅ E`.

### A.6 **The III.4.8 proof itself** (book p.71, verbatim skeleton)

> PROOF. If `φ(P) = O` for all `P ∈ E`, there is nothing to prove. Otherwise, `φ`
> is a finite map, so by (II.3.7), it induces a homomorphism
> `φ_* : Pic⁰(E₁) ⟶ Pic⁰(E₂)` defined by `φ_*(class of Σ nᵢ(Pᵢ)) = class of Σ
> nᵢ(φ Pᵢ)`. On the other hand, from (III.3.4) we have *group isomorphisms*
> `κᵢ : Eᵢ ⟶ Pic⁰(Eᵢ)`, `P ↦ class of (P) − (O)`. Then, since `φ(O) = O`, we
> obtain the following commutative diagram:
> ```
>      E₁  --κ₁(≅)-->  Pic⁰(E₁)
>      |φ                 |φ_*
>      v                  v
>      E₂  --κ₂(≅)-->  Pic⁰(E₂).
> ```
> Since `κ₁, κ₂, and φ_*` are all group homomorphisms and `κ₂` is injective, it
> follows that `φ` is also a homomorphism. ∎

The two non-trivial facts the proof relies on:
- **F1**: `φ_*` is a *well-defined group homomorphism on Pic⁰* — i.e. the divisor
  pushforward `Σnᵢ(Pᵢ) ↦ Σnᵢ(φPᵢ)` descends to divisor classes, which means
  **`φ_*` sends principal divisors to principal divisors** (II.3.7 / II.3.6 for
  the finite map `φ`).  THIS is the only deep input. Everything else is "κ is a
  hom-iso" (III.3.4) and a diagram chase.
- **F2**: the square commutes, i.e. `κ₂(φ P) = φ_*(κ₁ P)`, i.e.
  `φ_*((P) − (O)) ∼ (φP) − (φO) = (φP) − (O)`. This is immediate from the
  pushforward definition `φ_*(Σnᵢ(Pᵢ)) = Σnᵢ(φPᵢ)` together with `φ(O)=O`.

### A.7 Dual isogeny `φ̂` (III.6.1 / III.6.2, book p.81–84) — context only

> **Theorem 6.1.** Let `φ : E₁ → E₂` be a nonconstant isogeny of degree `m`.
> (a) There exists a unique isogeny `φ̂ : E₂ → E₁` satisfying `φ̂ ∘ φ = [m]`.
> (b) As a group homomorphism, `φ̂` equals the composition
> `E₂ --(Q)↦(Q)−(O)--> Div⁰(E₂) --φ*--> Div⁰(E₁) --sum--> E₁`.

i.e. `φ̂ = σ₁ ∘ φ* ∘ κ₂`, where `φ*` here is the **divisor PULLBACK** (fibre sum
`Σ_{φP=Q} e_φ(P)·(P)`), and `σ₁ = κ₁⁻¹` is the III.3.4 section.
**III.6.1/6.2 is the sibling-topic's job, not this one.** The note below (e) gives
the exact dependency boundary. The III.4.8 task uses only the *pushforward* φ_*
(point map on divisors), NOT the *pullback* φ*.

---

## (b) Silverman's proof skeleton (the spine to mirror)

```
III.4.8  φ(P+Q)=φ(P)+φ(Q)
  ├─ (degenerate) φ ≡ O  ⟹  trivially a hom                       [A.6 line 1]
  └─ (nonconstant) φ finite:
       ├─ build φ_* : Pic⁰(E₁)→Pic⁰(E₂)  group hom                [F1, deep]
       │    = descent of  Σnᵢ(Pᵢ) ↦ Σnᵢ(φPᵢ)  to classes
       │    ⟸ φ_* sends principal ↦ principal           (II.3.7)
       ├─ κᵢ : Eᵢ ≅ Pic⁰(Eᵢ)  group ISO                 (III.3.4)  [proven in repo]
       ├─ square commutes:  κ₂∘φ = φ_*∘κ₁               (φ(O)=O)   [F2, easy]
       └─ diagram chase: κ₂ inj + (κ₁,φ_*,κ₂ homs) ⟹ φ hom        [easy]
```

The Lean spine is *already laid down in the project* (see (c)/§ Existing infra):
`AddHomProperty_of_picZero_witnesses` is exactly this chase, and `picZeroIsoE`
is exactly `σ = κ⁻¹`. The work is consolidation + discharging F1.

---

## (c) The leaves (ordered), with discharge / source ref / LOC

Notation: `E.Point` = mathlib `WeierstrassCurve.Affine.Point`; `Pic⁰` =
`Curves.SmoothPlaneCurve.PicProj₀`; σ = `Curves.projectiveDivisorSum` (descended:
`picZeroIsoE_allChar`); κ = `Curves.kappaDivisor` / `picZeroOfPoint`.

### LEAF 0 — Decide the faithful `Isogeny` carrier and migrate (CONSOLIDATION)

**Statement.** Make `HasseWeil.EC.Isogeny W₁ W₂` (morphism-based: `CurveMap`
function-field pullback + `pullback_ordAtInfty_nonneg` basepoint witness) the ONE
faithful isogeny, and **deprecate / re-express** `HasseWeil.Isogeny` (Basic.lean,
which carries `toAddMonoidHom` as free DATA = the axiomatized group hom).

- Discharge: refactor only. `EC.Isogeny` (IsogenyAG.lean:66) is already the
  faithful one — it is `CurveMap`-based and does NOT store the group hom; group-hom
  is its `AddHomProperty` *Prop* (IsogenyAG.lean:234). `Basic.Isogeny`
  (Basic.lean:61) is the non-faithful one (stores `toAddMonoidHom`).
- Source ref: A.1 (morphism with `φ(O)=O`); the group hom is a *theorem* (A.4),
  hence must not be a structure field.
- LOC: 0 new math; ~150 LOC of migration glue if Basic.Isogeny consumers are
  rewired. **Risk/decision point — see (f).** A *minimal* version keeps both and
  just provides a bridge `EC.Isogeny → Basic.Isogeny` once `AddHomProperty` is
  proven (≈30 LOC), avoiding a repo-wide refactor. Recommended: minimal bridge
  first; full migration is a separate cleanup ticket.

**Sub-point — strict `φ(O)=O`.** The current basepoint field
`pullback_ordAtInfty_nonneg` only says "`φ` defined at `O₁`" (regular ↦ regular),
NOT the strict `φ(O)=O` (IsogenyAG.lean:38–43 admits this caveat). For the III.4.8
diagram chase we need `toPointMap cd O = O`, which IS proven (`toPointMap_zero`,
IsogenyAG.lean:120, holds *by definition* of `toPointMap` on `.zero`). So strict
basepoint preservation at the POINT level is already free; the structural-field
strengthening is cosmetic for III.4.8 and can stay deferred. **No source obstacle.**

### LEAF 1 — κ : E ≅ Pic⁰(E) is a group isomorphism (Abel–Jacobi III.3.4)

**Statement (Lean).**
`Curves.picZeroIsoE_allChar W : Curves.SmoothPlaneCurve.PicProj₀ ⟨W⟩ ≃+ W.Point`
(this is σ = κ⁻¹), over `[IsAlgClosed F] [IsDedekindDomain R] [IsIntegrallyClosed R]`.

- Discharge: **ALREADY PROVEN** — `Curves/MillerAllChar.lean:644`
  `picZeroIsoE_allChar`, built from `afInputs_allChar` (line 636) =
  `⟨miller_hypothesis_holds_allChar, divZeroReduce_holds_allChar,
  noFinitePolesBridge_unconditional⟩`. All three components are sorry-free,
  char-uniform. The forward map on a class is `σ`
  (`picZeroIsoE_allChar_mk`, OneSubDualDivisor.lean:94).
- Source ref: III.3.4(a)(c)(d), book p.61–63 (A.5); the hom property is
  `κ(P+Q)=κ(P)+κ(Q)` (p.63), which in the repo is the `≃+` structure's `map_add`
  (already part of `picZeroIsoE_allChar`).
- LOC: 0 (done). **This is the single biggest "restored Pic⁰ infrastructure" win:
  the whole Abel–Jacobi iso the proof needs is present and proven.**

Caveat — base field: III.3.4 is stated over `K̄` (Silverman works geometrically).
`picZeroIsoE_allChar` needs `[IsAlgClosed F]`. For `E/𝔽_q` one applies it to
`W.baseChange F̄` and descends. **This is exactly the cross-topic dependency** —
see (e).

### LEAF 2 — the diagram-commute (square `κ₂ ∘ φ = φ_* ∘ κ₁`)

**Statement (Lean).**
`Curves.picZeroOfPoint W₂ (φ.toPointMap cd P) =
   pushforwardPicZeroOfWitness φ cd h_pres (Curves.picZeroOfPoint W₁ P)`.

- Discharge: **ALREADY PROVEN** — `EC/IsogenyAG/HomProperty.lean:135`
  `picZeroOfPoint_pushforwardPicZero`, which descends the divisor-level commute
  `pushforwardProjectiveDivisor_kappaDivisor` (PicZeroPushforward.lean:120, proven
  via `toPointMap_zero` so the `(O)`-term lands back at `∞`).
- Source ref: F2 / A.6 — "`φ_*((P)−(O)) = (φP)−(φO) = (φP)−(O)` since `φ(O)=O`".
- LOC: 0 (done).

### LEAF 3 — the diagram chase: κ₂ inj + homs ⟹ φ is a hom

**Statement (Lean).** `φ.AddHomProperty cd` from the four witnesses
(σ-vanishes-on-principal ×2, pushforward-preserves-principal, σ̄-injective).

- Discharge: **ALREADY PROVEN** — `HomProperty.lean:165`
  `AddHomProperty_of_picZero_witnesses` is *exactly* Silverman's chase (the `calc`
  at lines 214–228). And `AFConditional.lean:281` `AddHomProperty_of_AFInputs`
  packages it taking `AFInputs` + `h_pres`; the σ-vanish and σ̄-inj witnesses are
  *derived* from `AFInputs` (`a.h_van`, `a.h_inj` — AFConditional.lean:221,255).
- Source ref: A.6, final sentence ("κ₂ injective + κ₁,κ₂,φ_* homs ⟹ φ hom").
- LOC: 0 (done).

### LEAF 4 — **F1 / `h_pres`: φ_* sends principal divisors to principal** ⚑ THE GAP

**Statement (Lean).** For an isogeny `φ : EC.Isogeny W₁ W₂` with a point-map
witness `cd`:
```lean
∀ D : ProjectiveDivisor ⟨W₁⟩,
  D ∈ ⟨W₁⟩.projPrincipalSubgroup →
  pushforwardProjectiveDivisor φ cd D ∈ ⟨W₂⟩.projPrincipalSubgroup
```
where `pushforwardProjectiveDivisor φ cd (Σnᵢ(Pᵢ)) = Σnᵢ(φ Pᵢ)`
(PicZeroPushforward.lean:36).

- Discharge: **GENUINELY NEW / the sole undischarged input.** Grep confirms
  `h_pres` is *carried as a hypothesis at every call site* and never proved
  (only consumer: HomProperty.lean:128; producers AFConditional.lean:288,
  NoFinitePolesBridge.lean:298 — all take it as a hyp).
- Source ref: II.3.7 (a finite morphism induces a well-defined `φ_*` on `Pic⁰`)
  / II.3.6 (`div(φ_* f) = φ_*(div f)`, the pushforward-of-principal-is-principal
  is exactly `φ_*(div f) = div(N_{φ} f)` for the norm/conorm `N_φ f ∈ K(E₂)`).
- LOC: **the hard leaf, ~250–450 LOC**, see (d) NEW-1 for the decomposition.

**THE SUBTLETY THAT MAKES THIS NON-TRIVIAL (and the faithfulness fault-line):**
`pushforwardProjectiveDivisor` is defined via `φ.toPointMap cd`, the POINT map,
which is gated on a `Curves.CurveMap.CoordHom` (an affine coordinate-ring lift of
`φ*`). Silverman's `φ_*` on Div⁰ is NOT the point-map pushforward — it is the
finite-morphism pushforward of divisors (II.3.6), defined for EVERY isogeny
without a coordinate-ring lift. Two routes:

  - **Route 4a (point-map pushforward, matches the existing repo plumbing).**
    Prove `h_pres` for the *point-map* pushforward. For a principal `D = div(f)`,
    `φ_*(div f)` = `Σ_P ord_P(f) · (φP)`. To show this is `div(g)` for some
    `g ∈ K(E₂)`, the clean route is the σ-criterion (Abel III.3.5, repo
    `Curves.miller_hypothesis_holds_allChar` ⟹ a divisor is principal iff
    deg = 0 ∧ σ = O): degree is preserved (`degree_pushforwardProjectiveDivisor`,
    DONE) and `σ(φ_* div f) = Σ ord_P(f)·φP = φ(Σ ord_P(f)·P) = φ(σ(div f)) =
    φ(O) = O` — **BUT this last step `Σ ord_P(f)·φP = φ(Σ ord_P(f)·P)` IS the
    group-hom property of φ, i.e. CIRCULAR.** This circularity is real and is the
    reason `h_pres` cannot be discharged by the σ-criterion. ✗

  - **Route 4b (norm/conorm pushforward, source-faithful II.3.6).** Define the
    *divisor* pushforward of the finite morphism via the field-norm conorm:
    for `f ∈ K(E₁)`, `N_φ(f) := Norm_{K(E₁)/φ*K(E₂)}(f) ∈ K(E₂)` (repo:
    `CurveMap.pushforward`, CurveMap.lean:257, ALREADY DEFINED and multiplicative).
    Then `div(N_φ f) = φ_*^{div}(div f)` where `φ_*^{div}` is the
    *valuation-theoretic* pushforward `Σ_Q (Σ_{P↦Q} ord_P f)·(Q)` (II.3.6). This is
    principal *by construction* (it's `div` of `N_φ f`). The remaining content is
    the COMPATIBILITY `φ_*^{div} = pushforwardProjectiveDivisor` (point-map form)
    on principal divisors — i.e. `Σ_{P↦Q} ord_P f` aggregates correctly and the
    image point of the divisor pushforward equals `φP`. This needs the
    fibre-structure (which points map to `Q`) but does NOT need φ to be a hom.
    **This is the genuinely-new, source-faithful work.** ✓ (preferred)

### LEAF 5 — Strict basepoint `φ(O)=O` at the structure level (OPTIONAL hardening)

**Statement.** Strengthen / add a field giving `toPointMap cd .zero = .zero`
*intrinsically* (not just by the `.zero ↦ .zero` definitional clause).

- Discharge: already free at the point level (`toPointMap_zero`, IsogenyAG.lean:120).
  Skippable for III.4.8. Source: A.1.
- LOC: 0 (or ~20 if a strict `0 < ord` field is added — cosmetic).

### LEAF 6 — package the unconditional `AddHomProperty` once F1 lands

**Statement (Lean).**
```lean
theorem EC.Isogeny.addHomProperty (φ : EC.Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    [IsAlgClosed F] [IsDedekindDomain R₁] [IsDedekindDomain R₂]
    [IsIntegrallyClosed R₁] [IsIntegrallyClosed R₂] :
    φ.AddHomProperty cd
```
and the bundled `toAddMonoidHomOfWitness` (IsogenyAG.lean:241).

- Discharge: `AddHomProperty_of_AFInputs φ cd (afInputs_allChar W₁) (afInputs_allChar W₂)
  h_pdz₁ h_pdz₂ (LEAF 4)` — a one-liner once LEAF 4 (`h_pres`) is a theorem.
  `h_pdz` (PrincipalImpliesDegZero) is `principal_mem_degZero` (used at
  NoFinitePolesBridge.lean:306, already discharged).
- Source ref: A.4 / A.6 conclusion.
- LOC: ~30 (wiring + the alg-closed instance bookkeeping).

### LEAF 7 — descend to `E/𝔽_q` (the K-rational consequence)

**Statement.** `AddHomProperty` for `φ : EC.Isogeny W W` over a finite `K` (not
alg-closed), by base-changing to `K̄`, applying LEAF 6, and descending along the
inclusion `E(K) ↪ E(K̄)`.

- Discharge: GENUINELY NEW glue, but standard — `Affine.Point.map` of the
  base-change ring hom is injective and an `AddMonoidHom` (mathlib gives
  `Affine.Point.map` as an `AddMonoidHom`, per MEMORY note). A hom over `K̄`
  restricts to a hom over `K`.  This **may be the sibling base-change topic's
  deliverable** — see (e).
- Source ref: III.4.8 is geometric (`P,Q ∈ E`, i.e. `E(K̄)`); the `K`-rational
  statement is the restriction.
- LOC: ~60–120 (depends on existing base-change infra; `IsogenyBaseChange.lean`
  exists).

---

## (d) Genuinely-new definitions / lemmas needed (with signatures)

### NEW-1 — `h_pres` via the norm conorm (LEAF 4, Route 4b). THE math.

Decomposition of "φ_* preserves principal":

```lean
-- (i) The valuation-theoretic divisor pushforward of a finite curve map.
--     (NOT point-map-gated; defined from the fibre valuations.)  ~II.3.6.
noncomputable def CurveMap.pushforwardDivisorVal (φ : CurveMap C₁ C₂)
    (D : ProjectiveDivisor ⟨C₁⟩) : ProjectiveDivisor ⟨C₂⟩
-- support: image points; coeff at Q = Σ_{P ↦ Q} (coeff_P D).

-- (ii) div of the conorm = pushforward of div  (THE principal lemma, II.3.6).
theorem CurveMap.projectiveDivisorOf_pushforward_eq_pushforwardDivisorVal
    (φ : CurveMap C₁ C₂) (f : C₁.FunctionField) (hf : f ≠ 0) :
    projectiveDivisorOf ⟨C₂⟩ (φ.pushforward f) =
      φ.pushforwardDivisorVal (projectiveDivisorOf ⟨C₁⟩ f)
-- ⟹ pushforwardDivisorVal of a principal divisor is principal, BY CONSTRUCTION.

-- (iii) compat: on an ELLIPTIC isogeny the val-pushforward agrees with the
--       point-map pushforward (needs the image point of the fibre = φ P).
theorem EC.Isogeny.pushforwardProjectiveDivisor_eq_pushforwardDivisorVal
    (φ : EC.Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (D : ProjectiveDivisor ⟨W₁⟩) :
    pushforwardProjectiveDivisor φ cd D = φ.toCurveMap.pushforwardDivisorVal D
-- on principal D suffices; this is where fibre↔point-image is used.

-- (iv) h_pres falls out:
theorem EC.Isogeny.pushforward_preserves_principal
    (φ : EC.Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (D) (hD : D ∈ ⟨W₁⟩.projPrincipalSubgroup) :
    pushforwardProjectiveDivisor φ cd D ∈ ⟨W₂⟩.projPrincipalSubgroup
```

Hardest sub-leaf: (ii), `div(N_φ f) = φ_*(div f)`. In a Dedekind / DVR setting
this is `ord_Q(N_φ f) = Σ_{P↦Q} f_{P/Q}·ord_P(f)` with inertia degrees — mathlib
has the relevant `Ideal.ramificationIdx`/`inertiaDeg`/`Algebra.norm` API and the
repo already uses `Ideal.sum_ramification_inertia`
(CurveMap.lean:411 `sum_ramificationIdx_mul_inertiaDeg_eq_degree`). The norm-valued
divisor-pushforward identity is the new piece.

### NEW-2 — minimal `EC.Isogeny → Basic.Isogeny` bridge (LEAF 0, minimal route)

```lean
noncomputable def EC.Isogeny.toBasicIsogeny
    (φ : EC.Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (h : φ.AddHomProperty cd) : HasseWeil.Isogeny W₁ W₂ :=
  { pullback := φ.toCurveMap.pullback,
    toAddMonoidHom := φ.toAddMonoidHomOfWitness cd h }
```
Lets every Basic.Isogeny consumer be fed a *faithful* isogeny whose group-hom is
now a THEOREM, without a repo-wide refactor. (Existing `WithHom` bundle,
IsogenyAG.lean:494, is the analogous packaging — reuse its shape.)

### NEW-3 — K-rational descent (LEAF 7), if not owned by the base-change topic

```lean
theorem EC.Isogeny.addHomProperty_descend
    {K : Type*} [Field K] (W : Affine K) [W.IsElliptic]
    (φ : EC.Isogeny W W) (cd : …) :
    ∀ P Q : W.Point, φ.toPointMap cd (P+Q) = φ.toPointMap cd P + φ.toPointMap cd Q
```
via `picZeroIsoE_allChar (W.baseChange (AlgebraicClosure K))` + injective
`Affine.Point.map`.

---

## (e) Dependency order + cross-topic dependencies

**Internal order:** LEAF 1,2,3 are DONE (just cite). The critical path is
`LEAF 4 (h_pres) → LEAF 6 (package) → LEAF 7 (descend)`. LEAF 0/5 are
consolidation, do LAST (or minimal-bridge NEW-2 early). So:

```
   [DONE 1,2,3]   NEW-2 (bridge, optional early)
        │
   LEAF 4 (NEW-1: h_pres via norm conorm)   ← the whole job
        │
   LEAF 6 (package AddHomProperty, alg-closed)
        │
   LEAF 7 (NEW-3: descend to K)             ← maybe owned by base-change topic
        │
   LEAF 0 (full migration, cleanup)
```

**Cross-topic dependencies (the other two topics):**

1. **Abel–Jacobi / Pic⁰ topic (`σ ≅ E`, Miller, base-change of Pic⁰).** LEAF 1
   *consumes* `picZeroIsoE_allChar` and the `AFInputs` bundle. These are already
   proven, so this is a *citation* dependency, not a blocker — UNLESS that topic
   is refactoring `picZeroIsoE` / `kappaDivisor` / `projPrincipalSubgroup` names,
   in which case LEAF 4/6 must track the new API. **Coordinate names with that
   owner.** Also: the `[IsAlgClosed F]` requirement of LEAF 1/6 means the
   *base-change of Pic⁰* (Pic⁰(E_K̄)) and `Affine.Point.map` injectivity (LEAF 7)
   are shared infrastructure with the base-change topic.

2. **Dual-isogeny / III.6 topic (`φ̂`, divisor PULLBACK `φ*`).** III.4.8 (this
   topic) uses ONLY the divisor *pushforward* `φ_*` (point map on divisors). The
   dual `φ̂` (III.6.1) uses the divisor *pullback* `φ*` (fibre sum
   `Σ_{φP=Q}e_φ(P)(P)`, A.7). These are DIFFERENT maps. **No logical dependency
   either way** — but NEW-1(i) `pushforwardDivisorVal` and the dual topic's
   `pullbackDivisor` (OneSubDualDivisor.lean:116 `degree_pullbackDivisor`, already
   built for the Weil-pairing route) are *mirror constructions*; share the
   fibre-valuation lemmas (inertia/ramification, `Ideal.sum_ramification_inertia`)
   to avoid duplication. The dual topic's `divisorPushforwardDual` (δ = κ∘φ*∘κ⁻¹,
   OneSubDualDivisor.lean:63) is the analogue for PULLBACK — a good code template
   for NEW-1's class-descent step.

**No dependency on the Weil-pairing / Hasse-bound machinery** — III.4.8 is
upstream of all of it (it is used to PROVE the dual is a hom, hence the pairing).

---

## (f) Honest risks / hardest parts

1. **LEAF 4 (h_pres) is the entire mathematical content** and it has a real trap:
   the "easy" σ-criterion route (4a) is **CIRCULAR** (it presupposes
   `Σ ord_P(f)·φP = φ(Σ ord_P(f)·P)`, which IS φ being a hom). One MUST go via the
   norm conorm (4b, NEW-1) — `div(N_φ f) = φ_*(div f)` (II.3.6). This is genuinely
   new and is the standard "finite morphisms push divisors forward and preserve
   principality" theorem, which the repo does NOT have (it has the *pullback*-side
   for the Weil-pairing route, and `CurveMap.pushforward` the norm MAP, but not the
   norm↔divisor-pushforward identity). Estimate 250–450 LOC; the
   ramification/inertia bookkeeping at finite places + the image-point
   identification (NEW-1 iii) are the fiddly bits.

2. **The `CoordHom` gating is a faithfulness fault-line.** The repo's
   `pushforwardProjectiveDivisor` and `toPointMap` REQUIRE a `CoordHom` (affine
   coord-ring lift of φ*). But `[n]` for `n≥2` and `1−π` have NO affine `CoordHom`
   (their `x`-image has poles at torsion — IsogenyAG.lean:24, 403–407). So the
   *point map itself* is only defined where a `CoordHom` exists. III.4.8 as stated
   ("φ is a hom") is about the point map, so for `[n]`/`1−π` the current
   `AddHomProperty cd` form is **vacuous/unstatable without `cd`**. Silverman's
   φ_* sidesteps this — it's the divisor pushforward, not the point-map pushforward.
   **Genuine design question (raise with the user / Pic⁰ owner):** should the
   faithful `Isogeny` carry the point map intrinsically (projective coord model,
   so `[n]` has one), or should III.4.8 be re-stated at the divisor/σ level
   (`σ ∘ φ_*^{div} ∘ κ` is additive) so it holds for ALL isogenies including
   `[n]`/`1−π` *without* a `CoordHom`? The latter is more faithful and more useful
   downstream (it's what the dual-isogeny topic actually needs). **Recommend the
   divisor-level statement as the primary theorem**, with the point-map corollary
   only where a `CoordHom` is supplied.

3. **`[IsAlgClosed F]` requirement.** LEAF 1/6 are alg-closed-only (Silverman is
   geometric). The `K`-rational descent (LEAF 7) is standard but depends on
   base-change infra shared with the sibling topic; if that infra is mid-refactor,
   LEAF 7 slips. Quantify the coupling early.

4. **Consolidation blast radius (LEAF 0).** A full migration of `Basic.Isogeny →
   EC.Isogeny` touches MANY downstream files (MulByIntPullback, FrobeniusIsogeny,
   the whole WeilPairing tree, RouteC* — `mulByInt`, `frobeniusIsog` are
   Basic.Isogeny). This is high-risk churn for little math gain. **Strongly prefer
   the minimal bridge (NEW-2)**: keep Basic.Isogeny as a downstream *adapter*, make
   EC.Isogeny canonical, and prove group-hom once on EC.Isogeny. Treat full
   migration as an out-of-scope cleanup ticket.

5. **Lowest-risk framing of the deliverable.** Given (1)+(2): the highest-value,
   most-faithful, lowest-churn deliverable is **(a)** cite LEAF 1–3 as the proven
   Pic⁰ spine, **(b)** discharge LEAF 4 via NEW-1 (norm conorm, the real theorem),
   **(c)** state III.4.8 at the divisor/σ level so it covers all isogenies, and
   **(d)** derive the point-map `AddHomProperty cd` corollary where `cd` exists
   (Frobenius has one — IsogenyAG.lean:306). Avoid the full Basic→EC migration.
