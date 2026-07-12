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
  Depends: T-D5d. **✅ DONE (2026-07-08, axiom-clean).** The one Hopf leaf `deligne_operators`
  (= Tate Lemma 3.8.2) closed from the text, RR-only; Prop 3.8.1 = `exists_commutator_eq_pointConv_smul_one`.
- **[T-D5f] det kills commutator ⟹ `λ^n=1`** (A4) — `Matrix.det_mul`; `det(λI_n)=λ^n`.
  Depends: none (parallel). **✅ DONE (`pow_eq_one_of_smul_id_eq_commutator`).**
- **[T-D5g] `deligne_grouplike_pow_order`** (A-assembly) — `⟨T-D5e, T-D5f⟩`. Depends: T-D5e, T-D5f, T-D5c.
  **✅ DONE (2026-07-08, axiom-clean): `deligne_pointConv_pow` + `deligne_pointConv_pow_finrank`.
  ALL of Layer A now depends only on [propext, Classical.choice, Quot.sound].**
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

## T-D5e-core decomposition (`deligne_operators` — the single remaining Layer-A leaf) — ✅ CLOSED 2026-07-08

**RESOLVED (2026-07-08, axiom-clean, coordinator-directed close-from-text, RR-only).** `deligne_operators`
is proved; all of Deligne's Layer A now depends only on `[propext, Classical.choice, Quot.sound]`
(verified `#print axioms` on `deligne_operators`, `coev_relation`, `translationEquiv`, `psiAlgEquiv`,
`deligne_pointConv_pow`, `deligne_pointConv_pow_finrank`). The winning route (all in the new
`DeligneLeaf` section of `ForMathlib/CartierDual.lean`) — cleaner than the recorded plan below:
- **`psiAlgEquiv`**: the comparison R-algebra iso `M = A'_B ⊗_R A ≅ A'_{B⊗A}` (from
  `rTensorHomEquivHomRTensor`, A finite free, + a hand-proved convolution-multiplicativity `map_mul`).
  It converts every step below into honest convolution maps `A → B⊗A`, no explicit dual basis in the algebra.
- **`translationEquiv` (T-D5e-τ)**: τ = right translation as a genuine `A'_B`-algebra **automorphism**;
  inverse `translationEndo(φ∘S)`, both compositions = id by monoid algebra in the *commutative*
  convolution ring (`leftPointConv_mul_antipode`, antipode = convolution inverse — NO nested Sweedler,
  the plumbing-chain worry below dissolved).
- **`coev` + `coev_relation` (T-D5e-u, 3.8.2)**: `u = ∑ eᵢ'⊗eᵢ` is a unit because `psiAlgEquiv u =
  pointConv includeRight` (universal point, `isUnit_pointConv`) — so `u`'s unit-ness needed NO explicit
  dual-basis inverse, contra the "delicate piece" note below. Lemma 3.8.2 `τ(u)=u·(λ⊗1)` becomes, under
  `Ψ`, cocommutativity `∑φ(a₁)⊗a₂ = ∑φ(a₂)⊗a₁` (`comm_comul`) — the generator formula
  `psiAlgEquiv_translationEndo_tmul` keeps it basis-free (x enters only via `f(x)`).

The historical decomposition notes below are kept for provenance.

**Status (2026-07-08, historical):** All of Deligne's Layer A is proved + axiom-clean and committed EXCEPT
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

---

## LAYER B EXECUTION LOG (2026-07-08, p2) — Layer A DONE; bridge started

**Layer A CLOSED + axiom-clean** (`ForMathlib/CartierDual.lean`): `deligne_pointConv_pow_finrank`
(linear-monoid form) and now **`deligne_point_pow_eq_one`** — the *point-group* form
`(toConv φ) ^ (finrank R A) = 1` in mathlib's convolution `CommGroup (WithConv (A →ₐ[R] B))`
(antipode-inverse), obtained from the linear form via `AlgHom.toLinearMap_convPow`/`toLinearMap_convOne`
+ `toLinearMap`/`ofConv`/`toConv` injectivity. This is the **exact geometry-free consumable** the
bridge needs (`n • [point] = 0` ⟺ `(toConv φ)^n = 1`). Axiom-clean `[propext, Classical.choice, Quot.sound]`.

**Substrate audit (Explore, 2026-07-08) — ALL of Layer B is absent** (project + mathlib):
- No group-object multiplication `m : D×_S D → D` from `IsSubgroup` (deliberately deferred,
  `GroupScheme/Subgroup.lean:108-111` — only the functor-of-points `Prop`).
- No affine-group-scheme ⇒ Hopf-algebra duality anywhere; `Mathlib/AlgebraicGeometry/Group/` is only
  `Abelian.lean` + `Smooth.lean`. Must be hand-built.
- No `D.subscheme` = `Spec`/`IsAffine`/`finrank ↔ Module.finrank` lemma (get affineness externally
  via `isAffine_of_isAffineHom`, only after the base is affine).
- **Free-vs-projective gap**: geometry gives `Module.Projective` (`projective_of_finitePresentation`);
  Deligne needs `Module.Free` → must Zariski-localise the base to trivialise `A`.
- **Reusable templates found**: `WeilPairing/EtaleDescent.lean` `torsionAlgebra` (affine group scheme →
  finite algebra, over a field) + `torsionAlgebraPointsEquiv` (points ↔ alg-homs via `ΓSpec` adj +
  `isoSpec`); `GroupScheme/MuN.lean` `muNPointsEquiv`/`_mul` (representable group law + points). Both
  lack the Hopf/comultiplication and the group-law↔convolution identification — the genuinely new work.

**Refined leaf decomposition (file `GroupScheme/DeligneOrder.lean`, imports {ExactOrder, CartierDual}):**
- **L1** general box `smul_eq_zero_of_factors'` (arbitrary `S`, `T`-point `Q`) ⟶ **affine core**
  `smul_eq_zero_of_factors_affine` (base `Spec R`, `Q : E.Section`). Reduce via base-change along `g`
  (→ section: `Point.asSection`, `Point.baseChangeEquiv`, `IsSubgroup.baseChange` — all proven) then
  cover `S` by affines + locality of morphism equality on the section base. *Routine but formal.*
- **L2 ✅ DONE** — `subgroupAlgebra` (`Algebra R Γ(D.subscheme, ⊤)`) + `subgroupAlgebra_finite`
  (`Module.Finite`), via `isAffine_of_isAffineHom` + the `torsionAlgebra` idiom. Green, no sorry.
- **L3** (the absent bulk) — comultiplication `Δ : A →ₐ[R] A ⊗_R A` dual to `m : D×_S D → D` (Yoneda:
  sum of the two universal `D×D`-points factors through `D` by `IsSubgroup`); counit dual to unit
  section; antipode dual to inversion. Needs `Spec(A⊗_R A) ≅ D.subscheme ×_{Spec R} D.subscheme`
  (product of affines). ⟹ `HopfAlgebra R A`.
- **L4** commutative + cocommutative (`IsCocomm R A`) from commutativity of the curve group law.
- **L5** `A` finite projective → localise `Spec R` over a free-trivialising cover, apply Deligne per
  piece, glue (`N • Q = 0` local on `Spec R`).
- **L6** points `Q ∈ D(Spec B)` ↔ `φ : A →ₐ[R] B` (`ΓSpec` adj, `isoSpec`); curve law = convolution
  (dual to `Δ`); `N • Q ↔ (toConv φ)^N`, `0 ↔ 1`.
- **L7** assemble: `deligne_point_pow_eq_one` ⟹ `(toConv φ)^N = 1` ⟹ `N • Q = 0`.

**Final wiring** (end of development, resolves the import cycle): the box
`RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors` in `ExactOrder.lean` is discharged by making
`ExactOrder` import `DeligneOrder` (or relocating `IsSubgroup` to a shared low file) and calling
`smul_eq_zero_of_factors'`. Deferred until the machinery is sorry-free.

**[T-D5h-Δ] (boarded 2026-07-08, p2, per coordinator v10.27 + rule 3 — heavy definition, decomposed).**
`subgroupComul` (Δ) is the one intricate Hopf-dual map; the transport `Γ(D ×_{Spec R} D) ≅ A ⊗_R A`
is a confirmed multi-step iso chain, so it is boarded as its own leaf with this exact recipe
(all APIs verified present):
1. `Algebra R Γ(D×_R D)` via `bimulBase.appTop` (analogue of `subgroupAlgebra`; the base map of
   `D×D` is `bimulBase = pullback.fst ≫ structMap`).
2. The two projections `pr₁, pr₂ : D×D ⟶ D` are over the base (`prᵢ ≫ structMap = bimulBase`), so
   `Γ(prᵢ) = prᵢ.appTop` are R-algebra maps `A → Γ(D×D)`; `κ := Algebra.TensorProduct.lift Γ(pr₁)
   Γ(pr₂) (commute) : A ⊗_R A →ₐ[R] Γ(D×D)`.
3. `κ` is bijective: `D.subscheme.isoSpec` turns each `structMap` leg into `Spec.map structMap.appTop`
   (`arrowIsoSpecΓOfIsAffine` / `isoSpec_hom_naturality`), so `pullback structMap structMap ≅
   pullback (Spec.map structMap.appTop)² ≅ Spec(A ⊗_{Γ(Spec R)} A)` (`pullbackSpecIso`) ≅
   `Spec(A ⊗_R A)` (scalar tower `Γ(Spec R) ≅ R` via `ΓSpecIso`); `Γ` of that is `κ⁻¹` up to the
   `pullbackSpecIso_inv_fst/snd` projection pins.
4. `m : D×D ⟶ D` is over the base (`m ≫ structMap = bimulBase`, from `subgroupMul_subschemeι`), so
   `Γ(m) : A →ₐ[R] Γ(D×D)`; **`Δ := κ.symm.comp Γ(m)`**.
5. **Ship opaque interface in the same increment (v10.24(b)):** `subgroupComul_apply` (or the pin
   `κ ∘ Δ = Γ(m)`, i.e. `pr₁^*(Δa₁)·pr₂^*(Δa₂) = m^*(a)`) + `irreducible`, so the Hopf-axiom proofs
   never unfold Δ's construction (avoids the T-W7.1b whnf/kernel-poison wall).
Consumers: the Coalgebra/Bialgebra/Hopf axioms (L4). Until it lands, `subgroupComul` stays sorried;
downstream Hopf-instance work is gated on it. Next unblocked p2 item meanwhile: **L1 reductions**.

**Status**: skeleton green (2 intended sorries: affine core L3-L7, general box L1).

**L3 CRUX DE-RISKED ✅ (2026-07-08)** — the group-scheme multiplication `m : D ×_S D ⟶ D.subscheme`
from `IsSubgroup` (the piece *deliberately deferred* in `Subgroup.lean` and *absent* from mathlib)
is now PROVEN in `DeligneOrder.lean`: `bipt₁`/`bipt₂` (the two universal points of `D ×_S D`),
`exists_factor_bimul` (their curve-sum factors through `D`, by `IsSubgroup` at the universal point +
`AddSubgroup.add_mem`), `subgroupMul` (= `m`, extracted; well-defined by the mono `subschemeι`),
`subgroupMul_subschemeι` (defining eqn `m ≫ subschemeι = (bipt₁+bipt₂).1`). This validates the entire
"IsSubgroup → group object → Hopf" route — everything downstream (Δ = m^♯, Hopf axioms, convolution)
now rests on a proven foundation.

**Group-object DATA COMPLETE ✅** — added `subgroupUnit` (e : S ⟶ D.subscheme, from `0 ∈ D(S)`),
`subgroupInv` (n : D.subscheme ⟶ D.subscheme, from `-upt ∈ D(D)`), `upt` (universal point), all with
`_subschemeι` defining equations. The full group-scheme structure (m, e, n) on `D.subscheme` from
`IsSubgroup` is now proven.

**Dualization dependency CONFIRMED PRESENT ✅** — `AlgebraicGeometry.pullbackSpecIso R S T`
(`Mathlib/AlgebraicGeometry/Pullbacks.lean:719`): `pullback (Spec.map algᵣₛ) (Spec.map algᵣₜ) ≅
Spec (S ⊗[R] T)`, with `pullbackSpecIso_inv_fst/snd`/`hom_fst` projection lemmas. So over the affine
base, `Γ(D ×_{Spec R} D) ≅ A ⊗_R A` (via `Scheme.isoSpec` transport of `D.subscheme ≅ Spec A`), and
`Δ = Γ(m)` lands in `A ⊗_R A` as required. The dualization route is grounded.

**⟹ THE ENTIRE LAYER B ROUTE IS VALIDATED END-TO-END** — group-object-from-`IsSubgroup` proven
(the deferred/absent piece); dualization iso present; Deligne consumable present
(`deligne_point_pow_eq_one`); points-equiv templates present (`torsionAlgebraPointsEquiv`,
`muNPointsEquiv`). No genuinely-absent multi-week infra remains — the rest is bounded formal build.

**ALL DEPENDENCIES CONFIRMED PRESENT (2026-07-08) — no genuinely-absent infra anywhere in Layer B.**
Confirmed mathlib API for the Δ-construction transport (`Γ(D×_R D) ≅ A ⊗_R A`):
`Scheme.isoSpec` (`AffineScheme.lean:68`, `X ≅ Spec Γ(X,⊤)` for `[IsAffine X]`),
`Scheme.isoSpec_hom_naturality` (`:72`, `f ≫ Y.isoSpec.hom = X.isoSpec.hom ≫ Spec.map f.appTop`),
`arrowIsoSpecΓOfIsAffine` (`:131`, `structMap ≅ Spec.map structMap.appTop` as an arrow), then
`pullbackSpecIso` (`Pullbacks.lean:719`) + `Scheme.ΓSpecIso`. Δ = `Γ(subgroupMul)` = `m.appTop`
post-composed with `Γ(D×_R D) ≅ A ⊗_R A`. Points (L6): `torsionAlgebraPointsEquiv` template
(`ΓSpec.adjunction.homEquiv` + `isoSpec`). Localise-to-free (L5): `projective_of_finitePresentation`
(`Flat/EquationalCriterion.lean:288`) + a free-trivialising basic-open cover. Reductions (L1):
`Point.asSection`/`asSection_zsmul`, `Point.baseChangeEquiv` (`≃+`), `Point.pull_add`/`_zsmul`/`_zero`,
`RelEffCartierDiv.IsSubgroup.baseChange`, `RelEffCartierDiv.baseChange` — all proven. The Δ/Hopf
leaf statements are now STATED (`subgroupComul`/`subgroupCounit`/`subgroupAntipode` sorried, green).

Next (downstream of the validated route): group AXIOMS as scheme equations (m assoc, unit/inv laws,
via the mono `subschemeι` + curve group axioms on pullback products; `pullback.lift`/`.map` for the
product morphisms) → dualize m/e/n to `Δ : A →ₐ[R] A ⊗_R A`, `ε : A →ₐ[R] R`, antipode over the
affine base (`Γ`-functor + `pullbackSpecIso` + `isoSpec`) → `HopfAlgebra R A` + `IsCocomm` (L4) →
localise-to-free (L5, `projective_of_finitePresentation` gives PROJ) → points↔convolution (L6) →
assemble (L7); plus the L1 reduction (general → affine). Sub-tickets T-D5h(=L2✅, L3-data✅,
axioms/Δ/Hopf/L4), T-D5i(=L6), T-D5j(=L7), T-D5k(=L1+box).

---

**L1 general→section reduction LANDED (2026-07-08, p2)** — `smul_eq_zero_of_factors'` (the box shape
of `RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors`, arbitrary base `S` + arbitrary `T`-point
`Q`) is now a **real proof** reducing to `smul_eq_zero_of_factors_section` (section box) — no longer
sorried. `#print axioms` = `[propext, sorryAx, Classical.choice, Quot.sound]` (sorryAx only from the
two consumed leaves). The reduction (all axiom-clean):
- **factoring transport** — `asSection Q` factors through `(D.baseChange g).ideal.subscheme` iff `Q`
  factors through `D.ideal.subscheme`: `baseChange_ideal` + `IdealSheafData.exists_factor_comap_iff`
  + `Point.asSection_val_fst` (term-mode `.trans`, NOT `rw` — the `(E.baseChange g).E` vs
  `pullback E.π g` defeq is not syntactic; `rw`/`simp` hit the semireducibility wall, exactly the
  trap flagged in `asSection`'s docstring). Divisor subgroup-ness base-changes via
  `RelEffCartierDiv.IsSubgroup.baseChange`.
- **asSection descent** — `Point.asSection E g` is injective (`Subtype.ext` + `asSection_val_fst` on
  the fst-leg) and sends `0↦0` (from `asSection_zsmul` at `n=0` + `zero_zsmul`), and intertwines
  `zsmul` (`asSection_zsmul`); so `(N:ℤ) • asSection Q = 0 ⟹ (N:ℤ) • Q = 0`.
- **boarded leaf `[T-D5h-degBC]`** — `degree_baseChange_eq`: relative degree (fibre finrank of the
  finite flat structure map) is base-change invariant. Sole genuinely-absent input; sorried with
  recipe (`Module.finrank_baseChange` fibrewise). Everything else in L1 is proven.

Remaining DeligneOrder.lean sorries (4): affine core (`smul_eq_zero_of_factors_affine`), Δ
(`subgroupComul`, boarded T-D5h-Δ), section box (`smul_eq_zero_of_factors_section`, needs affine
cover of `S`), degree (`degree_baseChange_eq`, boarded T-D5h-degBC). Next p2: section box→affine
core (cover `S` by affine opens + locality of the `S ⟶ E.E` equation), then the Hopf/Δ/L5/L6/L7
chain feeding the affine core.

---

**Δ (comultiplication) BUILT (2026-07-08, p2)** — `subgroupComul` is now a **real definition**, not a
sorry: `Δ = κ⁻¹ ∘ Γ(m)`, with the full supporting κ machinery landed axiom-clean and the opaque
interface shipped in the same increment (coordinator v10.24(b)). The pieces (all in AffineHopf,
`variable {R} (E) {D}`):
- `biproductAlgebra` — `R`-algebra on `Γ(D ×_{Spec R} D, ⊤)` via `bimulBase` (mirrors
  `subgroupAlgebra`). ✅ axiom-clean.
- `bimulBase_eq_fst_structMap` / `_snd_structMap` — `bimulBase = fst/snd ≫ structMap` (the second
  via `pullback.condition`). ✅
- `subgroupProj₁` / `subgroupProj₂ : A →ₐ[R] Γ(D×_R D)` — `Γ(fst)` / `Γ(snd)`, `R`-linear by the
  `bimulBase_eq_*` facts (antipode-style `commutes'` collapsing the appTop composition via
  `Scheme.Hom.comp_appTop`). ✅ axiom-clean.
- `subgroupTensorCompare` (κ) `: A ⊗_R A →ₐ[R] Γ(D×_R D)` = `Algebra.TensorProduct.lift proj₁ proj₂
  Commute.all`. ✅ axiom-clean.
- `subgroupMul_structMap` — `m ≫ structMap = bimulBase` (from `subgroupMul_subschemeι` + the
  bipt-sum's Point property). ✅
- `subgroupComulHom` (Γ(m)) `: A →ₐ[R] Γ(D×_R D)` — `R`-linear by `subgroupMul_structMap`. ✅
- `subgroupComul` (Δ) `:= (AlgEquiv.ofBijective κ hbij).symm.toAlgHom.comp Γ(m)`. Rests only on the
  ONE boarded leaf below (`sorryAx` only). Marked `attribute [irreducible]`.
- **PIN** `subgroupTensorCompare_subgroupComul : κ (Δ a) = Γ(m) a` (via `AlgEquiv.apply_symm_apply`)
  — the v10.24(b) opaque interface; downstream (Hopf axioms, L6) uses ONLY this, never unfolds Δ.

Sole remaining Δ leaf: **`subgroupTensorCompare_bijective` `[T-D5h-κbij]`** (BOARDED) — κ is bijective,
i.e. `pullbackSpecIso` (`Γ(Spec S ×_{Spec R} Spec T) ≅ S ⊗_R T`) transported across
`D.subscheme.isoSpec` on each affine factor. This is the ONLY genuinely-heavy scheme-iso step in the
whole Δ construction; everything else is elementary. `#print axioms`: κ machinery = the standard
three; Δ + pin = standard three + `sorryAx` (no stray axioms).

DeligneOrder.lean sorries now (4): affine core, κ-bijectivity ([T-D5h-κbij]), section box, degree
([T-D5h-degBC]). Coordinator item (1)=Δ effectively DONE. Next unblocked p2 work: item (2) Hopf
axioms (`Coalgebra`/`Bialgebra`/`HopfAlgebra R A` + `IsCocomm`) from Δ/ε/antipode via the pins —
these need only the pin + the group-object scheme equations, NOT κ-bijectivity, so they are
unblocked now.

---

**κ-bijectivity [T-D5h-κbij] — foundation landed (2026-07-08, p2)**: `subgroupBiproduct_isAffine`
(`IsAffine (D ×_{Spec R} D)`, axiom-clean) — `D.subscheme` finite⟹affine over `Spec R`, so
`pullback.fst` is affine (`MorphismProperty.pullback_fst`) and the fibre product of affines over an
affine base is affine (`isAffine_of_isAffineHom`). This is what makes `Γ(D×_R D)` a genuine
coordinate ring and κ an iso. **Remaining κ crux** (still the sole heavy scheme-iso step of Δ):
show κ = `TensorProduct.lift Γ(fst) Γ(snd)` agrees with the `pullbackSpecIso`-transport iso
`D×_R D ≅ Spec(A ⊗_R A)` — i.e. on generators `κ(a⊗1)=Γ(fst)(a)`, `κ(1⊗a)=Γ(snd)(a)` match the
transport (built from `D.subscheme.isoSpec` on each factor + `pullbackSpecIso R A A` +
`arrowIsoSpecΓOfIsAffine`), whence κ is `Γ` of an iso, hence bijective. Bounded but fiddly
(isoSpec naturality + ΓSpec compatibility on the two tensor factors).

**Other boarded infra leaves surfaced this session:**
- **degree-BC [T-D5h-degBC]** `degree_baseChange_eq`: `Scheme.Hom.finrank_pullback_snd` EXISTS
  (`(pullback.snd f g).finrank y = f.finrank (g y)` for `[Flat f][IsFinite f]`), so the only gap is
  relating `(D.baseChange g).subschemeι ≫ (E.baseChange g).π` to `pullback.snd (subschemeι ≫ π) g`
  up to a source iso (comapIso chase; `finrank_comp_left_of_isIso` absorbs the iso). Bounded diagram
  lemma.
- **restrict_add** (NEW, needed for the L3/L4 Hopf LAWS): `Point.restrict` (GroupLaw.lean:144,
  `⟨k ≫ P.1, _⟩`) has NO additivity lemma. The scheme group axioms (m assoc/comm, unit, inverse —
  which dualize to the Coalgebra/Bialgebra/HopfAlgebra laws + IsCocomm) are proven by post-composing
  with the mono `subschemeι` and reducing to `E.Point` group identities transported along
  swap/reassoc pullback maps — every such transport needs `(P+Q).restrict k = P.restrict k +
  Q.restrict k`. Prove it first (from the group-object law on the pullback), then the scheme axioms,
  then dualize via the Δ/ε/antipode pins. This is the bulk of remaining L4.

Layer B status: L1 general→section ✅, Δ (comul) ✅ (κ-bij boarded), ε ✅, antipode ✅, group-object
data (m/e/n) ✅, D×_R D affine ✅. Remaining: κ-bij crux, Hopf LAWS (via restrict_add), L5/L6/L7,
affine core, section→affine cover, degree-BC. All bounded; no genuinely-absent multi-week infra.

---

**L4 infrastructure landed (2026-07-08, p2)** — two axiom-clean lemmas that gate the Hopf LAWS:
- **`Point.restrict_add`** — `Point.restrict E k (P+Q) = restrict E k P + restrict E k Q`. Mirrors
  `Point.pull_add` exactly: `restrict` = left-composition by `Over.homMk k` in `Over S`, which
  distributes over the point-group multiplication because `E.asOver` is a group object
  (`pointEquivOverHom_add` + `MonObj.comp_mul`; the Over-morphism witness `k ≫ g = k ≫ g` is `rfl`,
  cleaner than `pull`'s). NB `Point.restrict`/`Point.pull` take `E` **explicit** — dot notation on
  the `E.Point` Subtype misassigns args; write `Point.restrict E k P`.
- **`subgroupBiproduct_isAffine`** — `IsAffine (D ×_{Spec R} D)` (see κ-bij note above).

**Scheme group axioms — the route (next L4 work), with its one real snag:** each axiom (e.g.
commutativity `swap.hom ≫ m = m`, the `IsCocomm` input) is proven by post-composing with the mono
`subschemeι`, rewriting `m ≫ subschemeι = (bipt₁+bipt₂).1`, and pushing the `swap`/reassoc through
the bipt sum with `restrict_add` + `pullbackSymmetry_hom_comp_fst` (`swap.hom ≫ fst = snd`). **Snag:**
`Point.restrict E swap.hom (bipt₁+bipt₂) : E.Point (swap.hom ≫ bimulBase)` while `bipt₂ : E.Point
bimulBase` — the point addition is base-dependent, so equating the two sums needs the dependent
transport across `swap.hom ≫ bimulBase = bimulBase` (propositional, via `bimulBase_eq_snd_structMap`
+ `pullbackSymmetry_hom_comp_fst`). That base-transport of a point-over-a-base is the fiddly step to
solve (a `Point` congruence/`eqToHom` lemma, or an `Eq.mpr` on the base) — bounded, not blocked.
Once the axioms land, dualize each to its Hopf law through `Γ` + the Δ/ε/antipode pins →
`Coalgebra`/`Bialgebra`/`HopfAlgebra R A` + `IsCocomm`.

---

**L4 Hopf-laws foundation LANDED (2026-07-08, p2)** — the ratified `point_add_eq_lift` route works:
- **`point_add_eq_lift`** (axiom-clean): `(P+Q).1 = (lift (eqv P)(eqv Q)).left ≫ μ[E.asOver].left`.
  2-line proof (`pointEquivOverHom_add` + `Over.comp_left`), mirroring `PullSectionAdd`'s `hx`. The
  point-addition underlying-map spec — lets scheme group axioms be proven on underlying morphisms,
  transport-free.
- **`subgroupMul_comm`** (axiom-clean): `swap ≫ m = m` (scheme commutativity → `IsCocomm`). Route:
  `cancel_mono subschemeι` → `subgroupMul_subschemeι` → `point_add_eq_lift` on both bipt-sums →
  lift-swap via `Over.tensorObj_ext` (swap exchanges the two `bipt`s: `pullbackSymmetry_hom_comp_fst`/
  `_snd`) + `add_comm`.
- **KEY GOTCHA (cost real time):** `rw` AND `simp only` BOTH fail on compositions involving the Over
  tensor's `.left` (`(lift a b).left ≫ pullback.fst E.asOver.hom E.asOver.hom`) — "not type-correct
  under instances transparency" (the `(E.asOver⊗E.asOver).left` vs `pullback E.π E.π` defeq is
  semireducible). MUST use **pure term-mode** `congrArg`/`.trans` (like `pointBaseChangeFun_add`,
  `transportSection_add`). Projection helpers `projfst/projsnd : (lift a b).left ≫ pullback.fst/snd
  E.asOver.hom E.asOver.hom = a.left/b.left` via `(Over.comp_left ..).symm.trans (congrArg
  Over.Hom.left (lift_fst/snd ..))`. The swap-on-bipt facts (plain pullbacks, `rw`-safe) proven
  separately as `hsf/hss`.

Remaining L4: associativity, unit laws, inverse laws (same technique), then dualize each through the
Δ/ε/antipode pins → `Coalgebra`/`Bialgebra`/`HopfAlgebra R A` + `IsCocomm`. Then L5→L6→L7→affine core.

**L4 continuation — strategic note (2026-07-08, p2):** the remaining scheme group axioms (unit,
inverse, associativity) each reduce — via `point_add_eq_lift` at the `.1` (morphism) level, dodging
the base-transport — to the corresponding axiom of `E`'s OWN commutative group object (`E.asOver` is
a `CommGrpObj`): unit law of `m` ⟸ `upt + 0 = upt` (`add_zero`), inverse ⟸ `upt + (-upt) = 0`
(`add_neg`), assoc ⟸ `add_assoc` on the three universal points of `D ×_S D ×_S D`. So each is the
same shape as `subgroupMul_comm` (which used `add_comm`): `cancel_mono subschemeι` →
`subgroupMul_subschemeι` → `point_add_eq_lift` → identify the `restrict`ed `bipt`s' underlying maps
via the `projfst/projsnd` + the relevant pullback.lift/section facts → close with the `AddCommGroup`
law. **Reuse the `subgroupMul_comm` proof skeleton verbatim** (term-mode only on tensor `.left`).
Then dualize: IsCocomm ⟸ `subgroupMul_comm` + κ-intertwines-`TensorProduct.comm`-with-`swap.appTop`
+ κ-injective (boarded κ-bij); coassoc/counit/antipode laws similarly through the Δ/ε/antipode pins.
All the HopfAlgebra-instance Hopf laws rest on κ-bijectivity [T-D5h-κbij] — so **κ-bij is the true
critical unblocker**; prioritise it (foundation `subgroupBiproduct_isAffine` already landed).

**κ-BIJ + degree-BC DISCHARGED (2026-07-08, p2, axiom-clean, committed 5c295e2a/c7b55c1c).**
- **`subgroupTensorCompare_bijective` [T-D5h-κbij] — DONE.** κ = ⟨Γ(fst),Γ(snd)⟩ is Γ of the scheme
  iso `Spec(A⊗A) ≅ D×_R D` via transporting `pullbackSpecIso R A A` across `D.subscheme.isoSpec` on
  each factor. Helper `subgroupSpecAlgebraMap_eq` (base-compat: `Spec.map(algebraMap R A) =
  isoSpec.inv ≫ q` via `isoSpec_inv_naturality` + `isoSpec_Spec_inv` + `ofHom_hom`). Main: the iso
  `ρ = asIso (pullback.map … isoSpec.inv isoSpec.inv (𝟙 _) e₁ e₁)` (`pullback.map_isIso`); then
  `Spec.map κ = isoSpec.inv ≫ ρ.inv ≫ pullbackSpecIso.hom` proven by `pullback.hom_ext` (fst/snd)
  matching `κ∘includeLeft/Right = Γ(fst)/Γ(snd)` via `lift_comp_includeLeft/Right` +
  `pullbackSpecIso_inv_fst/snd`; bijectivity reflected through fully-faithful `Spec`
  (`Spec.fullyFaithful.isIso_of_isIso_map` + `isIso_op_iff` + `ConcreteCategory.isIso_iff_bijective`).
  Gotcha: `erw` (defeq) for `↑includeRight` vs `.toRingHom` and for `pullback.map ≫ fst` (abbrev→lift);
  `← Category.assoc` before the `pullback.lift_fst/snd`. **⇒ `subgroupComul` (Δ) + pin now axiom-clean
  too** (κ-bij was their sole leaf) — full comultiplication interface SOLID.
- **`degree_baseChange_eq` [T-D5h-degBC] — DONE.** finrank base-change: base-changed structMap =
  `inv toImage ≫ (pullback.snd D.subschemeι (pullback.fst π g) ≫ pullback.snd E.π g)`, the pasted
  pullback (`IsPullback.paste_vert`) of `q` along `g`; `finrank_comp_left_of_isIso` +
  `finrank_of_isPullback` give `= D.degree (g t) = N`. Term-mode `.trans` tail (finrank's instance
  transparency wall on `rw`). ⇒ `smul_eq_zero_of_factors'` now rests ONLY on the section box.

**DeligneOrder.lean: 4→2 sorries** — remaining: (1) affine core `smul_eq_zero_of_factors_affine`
(the L3-Hopf + L5-free + L6-points↔conv + L7 mountain — the master leaf), (2) section box
`smul_eq_zero_of_factors_section` (affine cover of S → affine core). Next: L3 Hopf structure —
scheme group axioms (unit/inv/assoc via the `subgroupMul_comm` skeleton) → `Coalgebra` (coassoc needs
a κ₃ triple-tensor transport `Spec(A⊗A⊗A) ≅ D×_R D×_R D`, same technique as κ-bij; counit laws via
the ε pin) → `Bialgebra.mk'` (Δ/ε already AlgHoms ⟹ easy) → `HopfAlgebra` (antipode laws via the
antipode pin) → `IsCocomm` (from `subgroupMul_comm`). Then L5 (localise Spec R to make A free) → L6 →
affine core.

**L3 SCHEME GROUP AXIOMS DONE (2026-07-08, p2, axiom-clean, committed 1a6e5ad3/80994bc8).**
All via a uniform point-level skeleton (NO Over-tensor gymnastics — dodges `point_add_eq_lift`):
`cancel_mono subschemeι` → `subgroupMul_subschemeι` → `key : uX ≫ (bipt₁+bipt₂).1 = (restrict uX
(bipt₁+bipt₂)).1` (rfl) → `Point.restrict_add` → identify each `restrict uX biptᵢ` with `0`/`upt`/
`-upt` **over the matching base `uX ≫ bimulBase`** (Subtype.ext at the `.1` level; use `hbase : uX ≫
bimulBase = subschemeι≫π` to bridge the zero point's base) → close with the `AddCommGroup` law.
- Helpers (PointRestrict): `point_zero_val` ((0).1 = g≫E.zero), `Point.restrict_zero`,
  `point_neg_val` ((-P).1 = P.1 ≫ mulByHom(-1)).
- `subgroupUnit_over`/`subgroupInv_over` (general-S section/over-base facts).
- `subgroupMul_unit_left` `(e×id)≫m=id` (zero_add), `subgroupMul_unit_right` `(id×e)≫m=id`,
  `subgroupMul_inv` `⟨n,id⟩≫m=structMap≫e` (neg_add_cancel).
- GOTCHA: `set uX := pullback.lift …` needs a TYPE ASCRIPTION when not pinned by `≫ m` (else the
  cospan legs are metavars → `sorry` in the pullback type). Compat proof: `rw [Category.id_comp];
  exact …_over` (NOT `← Category.assoc`).
Remaining scheme axiom: **associativity** `(m×id)≫m = (id×m)≫m` on the triple pullback (add_assoc on
three universal points) — same skeleton, more bookkeeping. Only needed for coassoc.

**DUALIZATION ROUTE (the L3 crux, next) — the reusable intertwining.** Each Hopf law = Γ-pullback of
a scheme axiom via the gateway lemma:
  **`κ-intertwine`**: for `f : W ⟶ D×_S D` a morphism *over S* (W affine), `f.appTop ∘ κ =
  Algebra.TensorProduct.lift (Γ(f≫fst)) (Γ(f≫snd))` (both A-algebra homs A→Γ(W)). Proof:
  `Algebra.TensorProduct.ext` — agree on includeLeft/Right, `f.appTop∘proj₁ = (f≫fst).appTop` by
  `comp_appTop`; `proj₁ = fst.appTop` (subgroupProj₁ def). Needs `f over S ⟹ f.appTop is R-alg hom`
  (the subgroupProj₁ packaging, generalised).
Then:
- **Left counit** `(ε⊗id)∘Δ = mk 1` (⟺ via `TensorProduct.lid` `lid∘(ε.rTensor)∘Δ = id`): apply
  κ-intertwine with `f = uL = (e×id map)` — `uL.appTop∘κ = lift(Γ(uL≫fst),Γ(uL≫snd)) =
  lift(Γ(structMap≫e), Γ(𝟙)) = lift(εA, id) = lid∘(ε⊗id)` (εA = algebraMap∘ε = (structMap≫e).appTop);
  then `(lid∘(ε⊗id))(Δa) = uL.appTop(κ(Δa)) = uL.appTop(Γ(m)a)` [pin] `= (uL≫m).appTop(a)`
  [comp_appTop] `= 𝟙.appTop(a) = a` [subgroupMul_unit_left]. Right counit: symmetric (uR, unit_right).
- **Antipode laws**: κ-intertwine with `f = ⟨n,id⟩`/`⟨id,n⟩` + `subgroupMul_inv`.
- **Coassoc**: needs κ₃ `Spec(A⊗A⊗A) ≅ D×_S D×_S D` (κ-bij technique iterated) + scheme-assoc.
- **Bialgebra.mk'**: Δ, ε already AlgHoms ⟹ counit_one/comul_one/…_mul are `map_one`/`map_mul`.
- **HopfAlgebra**: antipode = subgroupAntipode + the two antipode laws. **IsCocomm**: from
  `subgroupMul_comm` + κ-intertwine on `swap`.
