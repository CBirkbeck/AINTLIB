# Development Plan: BB-DELIGNE — the order theorem for finite flat commutative group schemes

**Goal (geometric, the box to discharge).** Close
`ModularCurves.RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors`
(`LevelStructure/ExactOrder.lean:111`) and its consumer
`Section.HasExactOrder.smul_eq_zero` (T-D5): a subgroup divisor `D ⊂ E` of constant
degree `N` kills every point factoring through it, `(N : ℤ) • Q = 0`.

**Goal (abstract, the mathematical heart).** Deligne's theorem: *a commutative finite
locally free group scheme `G = Spec A` of rank `N` over an arbitrary base `R` is killed
by `N`* — every group-like element `λ ∈ (A'_B)` (i.e. every point `λ ∈ G(B)`) satisfies
`λ^N = 1`, for every `R`-algebra `B`.

**T-W7-independence.** Self-contained finite-group-scheme/Hopf-algebra theory. Does NOT
touch the scheme-level group law, RR, or `[N]`-étale. Buildable in parallel with the
A-lane.

---

## Source (READ IN FULL — Phase 1e Step 1 done)

**John Tate, "Finite Flat Group Schemes", in Cornell–Silverman–Stevens,
*Modular Forms and Fermat's Last Theorem* (Springer 1997), Chapter V.**
Local copy: `refs/ModularCurves/css-modular-forms-flt.pdf` (converted from the CSS djvu;
book-page = PDF-page − 18).

- §3.7 (III), **book p. 138**: states the theorem, notes the field/henselian case is
  proved there via the regular representation + Lemma 3.7.3, and *promises the general
  case*: verbatim —
  > "(In the next section, we will give Deligne's proof that a commutative finite locally
  > free group scheme over any base is killed by its order.)"
- §3.8 "The dual Hopf algebra and Cartier duality", **book pp. 143–145**: contains
  **Deligne's general-base proof**. Verbatim (book p. 144, bottom):
  > "The left `A'`-module `A' ⊗ A` is free of rank `n := [G : R]`, the order of `G`, and
  > (3.8.1) shows that the 'constant' matrix `λI_n` is a commutator in the group
  > `GL_n(A')`. If `A'` is commutative, that is, if `G` is commutative, then we can use
  > the determinant homomorphism `GL_n(A') → (A')*` to conclude that `λ^n = 1`. The same
  > holds for `λ ∈ G(B) ⊂ A'_B` for an arbitrary base ring extension `R → B`. Thus a
  > commutative finite flat group scheme is killed by its order."
  And book p. 145: *"The above is Deligne's proof of that fact, presented perhaps in a
  less comprehensible way than in [O-T]."*

Also read for context: Mumford AV §14 (field-case structure theory — NOT used; Deligne's
proof is simpler); Tate §3.1–3.7 (definitions, regular representation, connected-étale).

### Prose proof (Deligne, mirrors Tate §3.8)

Let `G = Spec A`, `A` a commutative Hopf algebra over `R`, locally free of rank
`n = [G:R]`. Let `A' := Hom_R(A, R)` be the dual `R`-module; by Cartier duality (§3.8) it
is the dual Hopf algebra, and because `G` is commutative `A'` is a **commutative**
`R`-algebra, again locally free of rank `n`. For any `R`-algebra `B`, the points
`G(B) = Hom_{R-alg}(A, B)` sit inside `A'_B = Hom_B(A_B, B)` precisely as the
**group-like elements** of the coalgebra `A'_B` (§2.9, §3.8).

Fix a point `λ ∈ G(B) ⊂ A'_B`. Consider the free rank-`n` `A'_B`-module `M := A'_B ⊗_B A_B`
and, inside `GL(M) = GL_n(A'_B)`, the automorphisms `τ_{id}` and `ρ` built from right
multiplications (Prop 3.8.1, Lemma 3.8.2). Proposition 3.8.1 exhibits scalar
multiplication by `λ` — the "constant matrix" `λ·I_n` — as a **commutator**
`τ_ρ τ_{id} ρ^{-1} ℓ^{-1}` in `GL_n(A'_B)`. Since `A'_B` is commutative, the determinant
`det : GL_n(A'_B) → (A'_B)^×` is a group homomorphism, so it kills commutators:
`det(λ·I_n) = 1`. But `det(λ·I_n) = λ^n`. Hence `λ^n = 1`. As this holds for every `B` and
every point `λ`, `G` is killed by `n`. ∎

---

## Decomposition (source-faithful to Tate §3.8)

### Layer A — the abstract Deligne theorem (Hopf-algebraic, mathlib-side)

- **A1 — Cartier dual as a commutative algebra.** For `A` a commutative Hopf `R`-algebra,
  finite locally free of rank `n`, the dual `A' = Module.Dual R A` is a commutative
  `R`-algebra (convolution/dual product), finite locally free of rank `n`.
  - Source: Tate §3.8, book p. 143 ("the dual `A'` … is a cocommutative Hopf algebra … the
    multiplication `A' ⊗ A' → A'` is dual to `m̃`").
  - mathlib: **GAP** — `Module.Dual` of a coalgebra as an algebra is *partially* present
    via convolution (`HopfAlgebra/Convolution.lean`, `LinearMap.mul` on `Module.Dual`);
    the finite-free duality anti-equivalence and the Hopf structure on `A'` are not
    packaged. → sub-tickets A1a (dual algebra structure), A1b (finite-free rank
    preservation), A1c (commutative when `A` cocommutative / `G` commutative).
- **A2 — points are group-like elements.** `G(B) = Hom_{R-alg}(A_B, B)` corresponds to the
  group-like elements of `A'_B`. mathlib: `RingTheory/HopfAlgebra/GroupLike.lean` exists →
  **discharge candidate** (verify the exact correspondence lemma).
- **A3 — the commutator relation (Prop 3.8.1).** For `λ ∈ G(B)`, scalar mult by `λ` on the
  free rank-`n` `A'_B`-module `A'_B ⊗ A_B` is a commutator in `GL_n(A'_B)`.
  - Source: Tate §3.8 Prop 3.8.1 + Lemma 3.8.2, book p. 144. **The heart.** Needs the two
    right-multiplication operators and the transpose identity. → sub-tickets A3a
    (operators `τ`/`ρ` + Lemma 3.8.2 transpose identity), A3b (Prop 3.8.1 commutator).
  - mathlib: **GAP** (build on `LinearMap`, `Module.End`, `Matrix.GeneralLinearGroup`).
- **A4 — determinant kills the commutator ⟹ `λ^n = 1`.** In `GL_n` over a commutative
  ring, `det` of a commutator is `1`; `det(λ·I_n) = λ^n`.
  - mathlib: `Matrix.det_mul`, `Matrix.det_smul`/`det_diagonal`, `Units.map det`. **DISCHARGE**
    (≤ 3 lemmas; det multiplicative + commutative ⟹ kills commutators is one line).
- **A-assembly — `deligne_grouplike_pow_order`**: `λ ∈ grouplike (A'_B) ⟹ λ^n = 1`. One-line
  `⟨A3, A4⟩` composition.

### Layer B — the geometric bridge (project-side, to the box)

- **B1 — the subgroup divisor is an affine group scheme.** `D.ideal.subscheme` (with the
  subgroup structure `D.IsSubgroup E`) is finite locally free over `S` of rank `N`
  (`degree = N` given), hence **affine**: `D.subscheme = Spec A_D` with `A_D` a finite
  locally free commutative Hopf `O_S`-algebra of rank `N`.
  - mathlib/project: `IsFinite ⟹ IsAffine` (used already in T-SG1/T-C0a: `isAffine_of_isAffineHom`);
    the Hopf structure comes from `D.IsSubgroup E`. → sub-tickets B1a (affine + Γ = `A_D`),
    B1b (Hopf structure from `IsSubgroup`).
- **B2 — a point factoring through `D` is a group-like element of `A_D'_B`.** The hypothesis
  `∃ h, h ≫ D.subschemeι = Q.1` gives `Q` as a `T`-point of `Spec A_D`, i.e. an element of
  `G_D(T) ⊂ (A_D')_{Γ(T)}` group-like. → sub-ticket B2.
- **B3 — `λ^N = 1` translates to `(N : ℤ) • Q = 0`.** The group-like power `λ^N` in `A_D'`
  corresponds to `N • Q` under `A2`/`B2`, and `λ^N = 1` ⟺ `N • Q = 0` (identity point).
  → sub-ticket B3.
- **B-assembly = the box** `smul_eq_zero_of_factors`: `⟨B1, B2, A-assembly, B3⟩`.

**Dependency graph.**
```
A1(a,b,c) ─┐
A2 ────────┼─→ A-assembly ─┐
A3(a,b) ───┤              │
A4 ────────┘              │
B1(a,b) → B2 ─────────────┼─→ B-assembly (= smul_eq_zero_of_factors) → T-D5
                          │
        (A-assembly) ─────┘
```

### Feasibility assessment

The abstract theorem (Layer A) is **feasible and well-scoped**: Deligne's proof is
elementary (Cartier dual + one commutator + `det`), entirely on mathlib's Hopf-algebra +
matrix API, with only the finite dual Hopf algebra (A1) and the commutator relation (A3)
as genuine new content. **No** Frobenius/Verschiebung, connected-étale, or Dieudonné
theory. The geometric bridge (Layer B) is standard `IsFinite ⟹ IsAffine` + Hopf-from-
subgroup + point-translation, reusing the T-SG1/T-C0a affine machinery. Realistic size:
Layer A ≈ 4–6 sessions (A1 the dual Hopf algebra is the bulk; a strong mathlib-upstream
candidate); Layer B ≈ 2–3 sessions. Multi-session, but each leaf is discharged or a
clean sub-development — no multi-week absent theory.

---

## Mathlib inventory

| Concept | Mathlib status | Action |
|---|---|---|
| Hopf/bi/coalgebra | `RingTheory.HopfAlgebra.*`, `Bialgebra.*`, `Coalgebra.*` | USE |
| Group-like elements | `RingTheory.*.GroupLike` | USE (A2) |
| Convolution on `Module.Dual` | `HopfAlgebra.Convolution` | USE/EXTEND (A1) |
| Dual **Hopf algebra** `A'` (finite free) | NOT packaged | DEFINE (A1) — upstream candidate |
| `Matrix.det` multiplicative, `det_smul` | `LinearAlgebra.Matrix.*` | USE (A4) |
| `IsFinite ⟹ IsAffine`, `Γ`-transport | project T-SG1/T-C0a, mathlib | USE (B1) |

## Generality decisions

- Layer A over an arbitrary commutative base ring `R` (Tate's generality; the whole point
  is *any* base). Universe-polymorphic. Typeclass: `HopfAlgebra R A` + `Module.Finite R A`
  + `Module.Free R A` (rank `n`) + cocommutativity (`A'` commutative).
- Keep the abstract theorem `deligne_grouplike_pow_order` **decoupled** from the geometric
  box, in a new `ForMathlib/` file (mathlib-upstream candidate). The box consumes it via
  the bridge.

---

## Ticket board (focused sub-project; append to main board on approval)

Files: `ModularCurves/ForMathlib/CartierDual.lean` (Layer A),
`ModularCurves/GroupScheme/DeligneOrder.lean` (bridge + box).

- **[T-D5a] `Module.Dual` Cartier dual algebra** (A1a) — dual product on `A' = Module.Dual R A`
  from the coalgebra comultiplication; `CommRing`/`Algebra R A'`. Depends: none. File: CartierDual.
- **[T-D5b] finite-free rank + commutativity of `A'`** (A1b,c) — `Module.Finite`/`Free`,
  rank `= rank A`; `A'` commutative when `A` cocommutative. Depends: T-D5a.
- **[T-D5c] points ↔ group-like** (A2) — `Hom_{R-alg}(A,B) ≃ grouplike (A'_B)`; verify
  against `HopfAlgebra/GroupLike.lean`. Depends: T-D5a.
- **[CLEANUP-D5-1]** `/cleanup` CartierDual.lean (after 3 tickets). Depends: T-D5c.
- **[T-D5d] operators + transpose identity** (A3a, Lemma 3.8.2) — `τ_λ`, `ρ` on `A'_B ⊗ A_B`;
  `(id⊗φ)(id) = (id⊗φ')(id)`. Depends: T-D5b.
- **[T-D5e] commutator relation** (A3b, Prop 3.8.1) — `λ·I_n` is a commutator in `GL_n(A'_B)`.
  Depends: T-D5d.
- **[T-D5f] det kills commutator ⟹ `λ^n=1`** (A4) — `Matrix.det_mul`; `det(λI_n)=λ^n`.
  Depends: none (parallel).
- **[T-D5g] `deligne_grouplike_pow_order`** (A-assembly) — `⟨T-D5e, T-D5f⟩`. Depends: T-D5e, T-D5f, T-D5c.
- **[CLEANUP-D5-2]** final `/cleanup` CartierDual.lean. Depends: T-D5g.
- **[T-D5h] subgroup divisor is affine Hopf algebra** (B1) — `D.subscheme = Spec A_D`, rank `N`.
  Depends: none. File: DeligneOrder.
- **[T-D5i] factoring point ↔ group-like** (B2). Depends: T-D5h, T-D5c.
- **[T-D5j] `λ^N=1 ↔ N•Q=0`** (B3). Depends: T-D5i.
- **[T-D5k] discharge the box** `smul_eq_zero_of_factors` — `⟨T-D5h, T-D5i, T-D5g, T-D5j⟩`.
  Depends: T-D5g, T-D5j. **MILESTONE.**
- **[CLEANUP-ALL-D5]** `/cleanup-all` before the milestone. Depends: all above.
- **[CLEANUP-FINAL-D5]** final pass. Depends: T-D5k.

Parallel capacity: T-D5a and T-D5f and T-D5h start immediately (3 workers).

---

## Prerequisites / open items before `/beastmode`

1. **Lean skeleton (Step 2.5) not yet written** — the next step is to state every ticket's
   lemma as `:= by sorry` in the two files and confirm `lake build` is green (sorries only).
   This is the first `/beastmode` action, or a follow-up `/develop --decompose` pass.
2. **Adversarial pass (Step 4.5) pending** on A3 (Prop 3.8.1 is the subtle leaf — the exact
   operator definitions and the commutator identity must be transcribed carefully from
   book p. 144, not reconstructed).
3. **A1 upstreamability**: the dual Hopf algebra is a clean mathlib-upstream target; build it
   in `ForMathlib/` with full API regardless.

---

## T-D5e-core decomposition (`deligne_operators` — the single remaining Layer-A leaf)

**Status (2026-07-08):** All of Deligne's Layer A is proved + axiom-clean and committed EXCEPT
the one Hopf leaf `deligne_operators` in `ForMathlib/CartierDual.lean`. Everything downstream
(`exists_commutator_eq_pointConv_smul_one` = Prop 3.8.1, `deligne_pointConv_pow` = T-D5g,
`deligne_pointConv_pow_finrank`) is proved *modulo* it via the axiom-clean assembly lemmas
`pow_eq_one_of_smul_id_eq_commutator`, `mulRight_conj_mulRight_inv`, `mulRight_tmul_one`.

**The leaf statement** (`M = S ⊗_R A`, `S = A'_B = WithConv (A →ₗ[R] B)`, `λ = pointConv φ`):
```
deligne_operators : ∃ (u : Mˣ) (τ : M ≃ₐ[S] M), τ (↑u) = ↑u * (pointConv φ ⊗ₜ[R] 1)
```
This is Tate's **Lemma 3.8.2** specialised to `φ = τ_λ` (CSS §3.8, book p. 144).

**mathlib grounding found:**
* `LinearAlgebra/Contraction.lean`: `dualTensorHom R M N : Dual R M ⊗[R] N →ₗ (M →ₗ N)`;
  `dualTensorHomEquivOfBasis b : Dual R A ⊗[R] A ≃ₗ (A →ₗ A)` (finite free) — the iso
  `A' ⊗ A ≅ End_R A`. The **coevaluation** `u_R := (dualTensorHomEquivOfBasis b).symm id ∈ A'⊗_R A`.
* `LinearAlgebra/Coevaluation.lean`: `coevaluation` (field version; for general R use the above).
* Base change: `M = A'_B ⊗_R A = A'_B ⊗_B A_B` (since `A'_B ⊗_B (B ⊗_R A) = A'_B ⊗_R A`); Prop 3.8.1
  is Tate's base-changed-from-R statement ("the same holds for λ ∈ G(B)").

**Sub-tickets (source-faithful, to build next):**
* **T-D5e-u**: the coevaluation `u ∈ M` is a *unit* of the tensor-algebra `M` (it is the group-like
  `id ∈ G(A)` ⊂ `A'_A`, so `IsGroupLikeElem`/antipode gives its inverse — NOT via the End iso, which
  is only R-linear not a ring map). Needs `M`'s group-like structure or a direct inverse.
* **T-D5e-τ**: `τ_λ : A_B → A_B` right-translation `= (λ ⊗ id) ∘ Δ` (λ the B-point), an S-algebra
  automorphism (λ group-like, Δ alg-hom; inverse via antipode); then `τ = id_{A'_B} ⊗_B τ_λ` on
  `M = A'_B ⊗_B A_B`.
* **T-D5e-3.8.2**: `τ(u) = u · (λ⊗1)` — Tate's Lemma 3.8.2: both sides are the element of `A'⊗A`
  corresponding to `τ_λ` (resp. its transpose `R_λ`) under `A'⊗A ≅ End_R A ≅ End_R A'`; the
  transpose of `τ_λ` (transpose of right-mult-by-λ) IS right-mult-by-λ on `A'`, giving `u·(λ⊗1)`.

This is a genuine multi-session dual-basis / base-change build; the leaf is precisely isolated so
the rest of Deligne's theorem stands on it and nothing else.

### T-D5e-core refinement (2026-07-08, after landing rightTranslationAlgHom)

Two findings that de-risk the remaining leaf:

1. **`τ` (T-D5e-τ) is UNBLOCKED — no dual-Hopf antipode needed.** `τ`'s inverse is right-translation
   by `λ⁻¹`, and `λ⁻¹` is the convolution inverse of the point, `= φ ∘ antipode_A` — which is
   `A`'s antipode (present in mathlib) via the already-proved `isUnit_pointConv` /
   `mul_pointConv_antipode_eq_one`. So `τ : M ≃ₐ[S] M` needs only `A`'s Hopf structure, NOT the
   Cartier-dual Hopf structure. Concrete construction chain (all algebra homs):
   ```
   τ := (absorb B into S) ∘ Algebra.TensorProduct.map (AlgHom.id R S) (rightTranslationAlgHom φ)
        -- S ⊗_R A --(id ⊗ (a↦∑φ(a₁)⊗a₂))--> S ⊗_R (B ⊗_R A) --(S⊗B→S via B-alg mult)--> S ⊗_R A
   ```
   `absorb`: `S ⊗_R (B ⊗_R A) ≅ (S ⊗_R B) ⊗_R A → S ⊗_R A` using `S` a `B`-algebra
   (`s ⊗ b ↦ s·algebraMap B S b`). Its inverse uses `rightTranslationAlgHom (φ∘S_A-conv-inverse)`.

2. **`u`'s unit-ness (T-D5e-u) is the ONE genuinely delicate piece.** `u = ∑ eⁱ⊗eᵢ` (coevaluation,
   via `dualTensorHomEquivOfBasis.symm id`) must be a unit of the *tensor-algebra* `A'⊗A` (whose ring
   structure is `A'`-convolution ⊗ `A`-mult, NOT `End`). Abstractly this is "u is group-like in the
   Cartier-dual Hopf algebra `A'_A`" — needs the dual-Hopf antipode mathlib lacks. BUT it should be
   closable by a DIRECT dual-basis computation exhibiting `u⁻¹` explicitly and verifying `u·u⁻¹ = 1`
   via the antipode identity `∑ eⁱ·(S eⱼ-twist)... = ε`, without the abstract structure. This is the
   Sweedler/dual-basis calculation to design source-faithfully next.

3. **Lemma 3.8.2** (`τ(u) = u·(λ⊗1)`) then follows from the dual-basis form of `u` + `τ`'s action.

Net: the leaf is in-reach (no genuinely-absent multi-week infra strictly required — `u`'s inverse is
an explicit dual-basis element), just a laborious dual-basis/base-change build. `τ` first (unblocked),
then `u`+inverse (dual-basis), then 3.8.2.

### T-D5e-τ empirical findings (2026-07-08) — the base-change plumbing chain

Probed the τ construction; it bottoms out at a chain of `WithConv`/base-change lemmas, each
needing its own proof (none automatic). Concrete findings:

* `IsScalarTower R B (A →ₗ[R] B)` — **automatic** (`inferInstance` ✓).
* `IsScalarTower R B (WithConv (A →ₗ[R] B))` — **NOT automatic**; needs transport through the
  `ofConv` bijection (a `WithConv.ofConv_smul`-style lemma: `ofConv (s • x) = s • ofConv x`).
  This is the first infra sub-ticket; once it lands, `ptS := (IsScalarTower.toAlgHom R B S).comp φ`
  gives the point-as-S-algebra-map.
* Then `τ`'s cleanest build is via the universal property: an `S`-algebra hom `S ⊗_R A → S ⊗_R A`
  from the `R`-algebra hom `g := (Algebra.TensorProduct.map ptS (AlgHom.id R A)).comp (comulAlgHom R A)`
  (`A →ₐ[R] S ⊗_R A`, `a ↦ ∑ ptS(a₁) ⊗ a₂`) via `Algebra.TensorProduct.lift` — avoids the
  assoc/absorb gymnastics. Inverse via `g` for the convolution-inverse point `φ ∘ antipode`.
* `u` (T-D5e-u): coevaluation `∑ eⁱ ⊗ eᵢ` with explicit dual-basis inverse `∑ eⁱ ⊗ (antipode-twist)`,
  `u·u⁻¹=1` by the antipode/dual-basis identity — a Sweedler computation, no abstract dual-Hopf.
* `τ(u) = u·(λ⊗1)` (Lemma 3.8.2): from the dual-basis forms.

**Order to build:** `ofConv_smul` transfer lemma → `IsScalarTower R B S` → `ptS` → `g` → `τ` (lift) →
`τ` inverse → `u` + `u⁻¹` (dual basis) → Lemma 3.8.2 → close `deligne_operators`. Multi-session but
each link is bounded and in-area (no absent multi-week mathlib theory strictly required).

### T-D5e-τ chain 1-4 DONE; remaining 3 pieces with Sweedler proofs (2026-07-08, coordinator-directed close-from-text)

Coordinator (v10, p2): source gate LIFTED — close `deligne_operators` from Tate css §3.8 pp.143-145
(verbatim quotes in docstring, no memory), RR-only (must prove). Chain links landed + axiom-clean:
`instIsScalarTowerWithConv`, `pointAlgHom`, `translationTarget`, `translationEndo`. VERIFIED faithful:
`translationEndo φ (s⊗a) = ∑ (s·ptS(a₁))⊗a₂` IS the base-changed `id_{A'}⊗τ_λ` (Tate p.144;
`λ(f₁)·μ = μ·ptS(f₁)`). Remaining, each a bounded Sweedler/dual-basis lemma:

* **τ auto-ness** — inverse point `φ' := φ.comp (HopfAlgebra.antipodeAlgHom R A) : A →ₐ[R] B` (antipode
  is an algHom for commutative A). Then `translationEndo φ ∘ translationEndo φ' = id`: on a generator
  `1⊗a`, compose → (coassoc) `∑ ptS_φ(a₁)·ptS_φ'(a₂) ⊗ a₃ = ∑ (φ⋆φ')(a₁)·1 ⊗ a₂`; `φ⋆φ'=ε`
  (convolution inverse, `∑φ(a₁)φ'(a₂)=ε(a)`) collapses to `1⊗∑ε(a₁)a₂ = 1⊗a` (counit). Build via
  `Algebra.TensorProduct.lift` uniqueness (agree on `1⊗a` generators) + `Coalgebra.Repr` Sweedler.
  Then `τ := AlgEquiv.ofAlgHom (translationEndo φ) (translationEndo φ') _ _`.
* **u (coevaluation) + unit** — `u := ∑ᵢ ιₘ(b.coord i) ⊗ b i ∈ M`, `b := Module.Free.chooseBasis R A`,
  `ιₘ : Dual R A → S`, `a' ↦ toConv (Algebra.linearMap R B ∘ₗ a')`. Inverse `u⁻¹ := ∑ᵢ ιₘ(b.coord i)⊗S(b i)`
  (antipode-twist); `u·u⁻¹=1` by dual-basis `∑ᵢ b.coord i (x) • b i = x` + antipode identity.
* **Lemma 3.8.2** `τ(u)=u·(λ⊗1)` — `translationEndo φ (∑ᵢ ιₘ(eⁱ)⊗eᵢ) = ∑ᵢ∑ ιₘ(eⁱ)·ptS(eᵢ₁)⊗eᵢ₂`;
  `u·(λ⊗1) = ∑ᵢ (ιₘ(eⁱ)·λ)⊗eᵢ`; equal by the dual-basis/Sweedler identity (Tate's "bit of linear
  algebra left to the reader", p.144). Key: `∑ᵢ ιₘ(eⁱ)·ptS(eᵢ₁) ⊗ eᵢ₂ = ∑ᵢ ιₘ(eⁱ)·λ ⊗ eᵢ` via
  `∑ᵢ eⁱ(·) eᵢ = id` and `λ = pointConv φ` acting as `ptS`.

Then `deligne_operators := ⟨u-as-unit, τ, lemma-3.8.2⟩`. Each piece is bounded; RR-terminates.
