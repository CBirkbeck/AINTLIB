# Decomposition — finishing Group A (T004/T005 + the T002 boundary)

*`/develop`, 2026-06-21. Source read directly: Diamond–Shurman (`/tmp/ds.txt`, agent aebc33dd).
T006 (`Newform.isFullEigenform`) + T003 (`newformEigenHom`) already DONE + axiom-clean.*

## Executive finding (source-faithfulness — BINDING)

**The deep input `heckeAlgℤ_finite : Module.Finite ℤ (heckeAlgℤ N k)` (T002) is unavoidable and is the
integral Eichler–Shimura structure.** DS's *only* "eigenvalues are algebraic integers" theorem
(**Thm 6.5.1**, `ds.txt:18066-18082`) is **weight-2-only** and runs through the **homology lattice
`H₁(X₁(N),ℤ)`** (free f.g. ℤ-module, `T_p` acts by an integer matrix → monic integer char-poly →
Cayley–Hamilton). Module-finiteness of `T_ℤ` is then the trivial `End_ℤ(free rank r) ≅ M_r(ℤ)`
linear algebra (**Ex 6.5.1**, `ds.txt:18385`).

**The q-expansion-lattice route is REJECTED (quote-or-delete).** DS has **no** q-expansion principle,
**no** Sturm bound, **no** integral-q-lattice for cusp forms (keyword sweep: the phrase
"q-expansion principle" never appears). The rational-coefficient basis (**Cor 6.5.6**) is *derived
from* the homology via Galois descent — **a consequence, not an input**. So the q-expansion route's
deep leaf ("the integer-q-expansion lattice is full rank") has no DS source and merely relocates the
same deep input. The existing **IHR (integral modular-symbol, weight-k Eichler–Shimura) roadmap is
the source-faithful route** and is kept (refined in Tranche 2 below).

**Consequence for the plan.** Split into:
- **Tranche 1 (BOUNDED, gate-passing, formalizable NOW)** — isolate `heckeAlgℤ_finite` as the single
  input and prove T004/T005 + the bad-prime coefficient link from it. All leaves discharged from
  mathlib / existing project code + DS weight-k formulas. **This is the immediately-actionable board.**
- **Tranche 2 (RESEARCH ROADMAP, gate does NOT pass)** — prove `heckeAlgℤ_finite` via integral
  Eichler–Shimura. Deep leaves (Manin presentation, period integral, injectivity). Kept as roadmap.

---

## Tranche 1 — bounded decomposition (the actionable board)

### Result T004: `coeffSeq_isIntegral (f : Newform N k) (n : ℕ+) : IsIntegral ℚ (coeffSeq f n)`
### Result T005: `instFiniteDimensionalCoeffField (f) : FiniteDimensional ℚ (coeffField f)`

Plain-English proof. Let `O_f = (newformEigenHom f).range ⊆ ℂ`, the ℤ-subalgebra of Hecke
eigenvalues. (i) `O_f` is module-finite over ℤ (surjective image of `heckeAlgℤ`, which is
`Module.Finite ℤ` by the FIH). (ii) Every coefficient `aₙ(f) = coeffSeq f n` lies in `O_f`: for a
*newform*, `aₙ(f) = λₙ = newformEigenHom f (heckeEnd⟨n⟩)` for **all** n (DS Thm 5.8.2 + eq 5.21).
(iii) `aₙ ∈ O_f` module-finite over ℤ ⟹ `IsIntegral ℤ aₙ` ⟹ `IsIntegral ℚ aₙ` (T004). (iv) `ℚ·O_f`
is a finite-dim ℚ-subalgebra of ℂ, a domain, hence a field containing every `aₙ`; `coeffField f ⊆ ℚ·O_f`
is therefore finite-dim over ℚ (T005).

### Leaves (in order)

- **L0 [T002-iface]** (API gap — the single isolated input):
  `instance heckeAlgℤ_finite : Module.Finite ℤ (heckeAlgℤ N k)`.
  - Status: **the one research-scale input** (Tranche 2 discharges it). Stated as the isolated
    interface; its proof is the roadmap. NOT a leaf — gate does not pass for its proof, but it is a
    clean, well-typed *hypothesis* everything below consumes (cf. the FD-e.2 pattern where the gate
    was sorry-free-in-body over a black-box input).
  - Source: DS Defn 6.5.2 (`ds.txt:18085`) + the finiteness claim (`ds.txt:18095-18096`,
    "viewing `T_ℤ` as a ring of endomorphisms of the finitely generated free Z-module `H₁(X₁(N),Z)`
    shows that it is finitely generated as well (Exercise 6.5.1)").

- **L1 [T004a]** (leaf — bad-prime coefficient link; project + DS eq 5.21):
  `coeffSeq f n = newformEigenHom f ⟨heckeEnd N k n, heckeEnd_mem n⟩`  for **all** `n : ℕ+`.
  - Sub-structure: (a) `Tₙf = λₙ • f` with `λₙ = newformEigenHom f (heckeEnd⟨n⟩)` — from T006
    `isFullEigenform` + T003 `eigenScalar`. (b) `a₁(Tₙ f) = aₙ(f)` for all n — DS eq (5.21),
    `ds.txt:15332`: *"a₁(Tₙ f) = aₙ(f) for all n ∈ ℤ⁺ (5.21)"*. (c) `a₁(λₙ•f) = λₙ·a₁(f) = λₙ`
    (`isNorm`: `a₁(f)=1`). Compose: `aₙ(f) = λₙ`.
  - **Coprime n**: already `coeffSeq_coprime_eq_eigenvalue` (NewformOrbit:127) + `newformEigenHom_heckeEnd`
    (T003). **Bad n**: (b) is the new sub-leaf — `fourierCoeff_heckeT_n_period_one` (FourierHecke:702)
    is coprime-only, so the bad-prime `a₁(Uₚ..f)=aₙ(f)` must come from the bad Fourier action
    (`heckeT_n_cusp_divN_coeff` FullEigenform:36 + the bad-prime FourierHecke machinery). Bounded.
  - Source: DS Prop 5.3.1 eq (5.14) `ds.txt:14037`, eq (5.21) `ds.txt:15332`, Thm 5.8.2
    `ds.txt:15370-15378` ("its Fourier coefficients are its Tₙ-eigenvalues … for all n").

- **L2 [T004b]** (leaf, mathlib): `Module.Finite ℤ ↥(newformEigenHom f).range`.
  - From L0 via the surjection `heckeAlgℤ ↠ range`. Discharged by `Module.Finite.of_surjective`
    (verified `RingTheory/Finiteness/Basic.lean:252`) applied to the range-restricted ring hom
    (`RingHom.rangeRestrict` surjective).

- **L3 [T004]** (leaf, mathlib + L1 + L2): `IsIntegral ℚ (coeffSeq f n)`.
  - `coeffSeq f n ∈ O_f` (L1), `Module.Finite ℤ O_f` (L2) ⟹ `IsIntegral ℤ (coeffSeq f n)` by
    `IsIntegral.of_finite ℤ` (verified `RingTheory/Algebraic/Integral.lean:102`, on the subtype
    element) ⟹ `IsIntegral ℚ` by `IsIntegral.tower_top` / `IsIntegral.map` of the
    `ℤ→ℚ` scalar tower. Then rewire `NewformOrbit.lean:442`.

- **L4 [T005]** (leaf, mathlib + L2): `FiniteDimensional ℚ (coeffField f)`.
  - `A := Algebra.adjoin ℚ (O_f : Set ℂ)`: `Module.Finite ℚ A` from `Module.Finite ℤ O_f` (extend
    scalars ℤ→ℚ; `Algebra.adjoin` of a module-finite set of integral elements is finite-dim). `A` is
    a domain (`⊆ ℂ`) and finite-dim over ℚ ⟹ a field (finite-dim domain over a field is a field).
    `coeffField f = IntermediateField.adjoin ℚ (range coeffSeq) ⊆ A` (each `aₙ ∈ O_f ⊆ A`, L1), and a
    sub-ℚ-space of a finite-dim ℚ-space is finite-dim. Then rewire `NewformOrbit.lean:452`.
  - Mathlib path: `Module.Finite` base change, `Algebra.IsIntegral.isField`/`isField_of_isIntegral_of_isField`
    or finite-dim-domain-is-field, `Submodule.finiteDimensional` (sub of finite-dim), `IsIntegral.fg_adjoin_singleton`
    (`IsIntegral/Basic.lean:104`) for the per-element integrality. (Exact lemma names to pin during /beastmode.)

### Source check (Tranche 1)
- eq (5.14): *"aₘ(Tₙf) = Σ_{d|(m,n)} χ(d) d^{k-1} aₘₙ/d²(f)  (5.14)"* — `ds.txt:14037`.
- eq (5.21): *"a₁(Tₙ f) = aₙ(f) for all n ∈ ℤ⁺   (5.21)"* — `ds.txt:15332`.
- Thm 5.8.2: *"Each such newform … satisfies Tₙ f = aₙ(f) f for all n ∈ ℤ⁺. That is, its Fourier
  coefficients are its Tₙ-eigenvalues."* — `ds.txt:15376-15378`.
- Thm 6.5.1 + Ex 6.5.1 (the L0 input): `ds.txt:18066-18096`, `18385`.
- Thm 6.4.5 (algebraic-integer criterion, used implicitly via mathlib `IsIntegral`): `ds.txt:17945-17954`.

### Attacks (Tranche 1)
1. *"O_f finite over ℤ but coeffField needs finiteness over ℚ — gap?"* → no: ℚ·O_f finite over ℚ
   (base change of a f.g. ℤ-module), and `coeffField ⊆ ℚ·O_f`. SURVIVES.
2. *"L1 bad-n: maybe aₙ ≠ λₙ at bad primes"* → DS Thm 5.8.2 explicitly extends `Tₙf=aₙf` to ALL n for
   **newforms** (the new∩old=0 / Main-Lemma argument) — and T006 already encodes exactly this
   (`isFullEigenform`). The only sub-leaf is `a₁(Tₙf)=aₙ(f)` for bad n, which is eq (5.21) (DS: all n).
   SURVIVES (with the bad-Fourier sub-leaf flagged).
3. *"finite-dim domain need not be a field"* → over a FIELD (ℚ) a finite-dim domain IS a field
   (Artinian domain). SURVIVES.
4. *"`IsIntegral.of_finite` needs the element in the finite algebra, but coeffSeq f n : ℂ not O_f"* →
   apply to the subtype element `⟨coeffSeq f n, mem⟩ : O_f`, then push integrality along `O_f ↪ ℂ`
   (`IsIntegral.map`). SURVIVES.

---

## Tranche 2 — `heckeAlgℤ_finite` (T002): research roadmap (gate does NOT pass)

**Source-faithful route = integral Eichler–Shimura (DS Ch. 6, weight-k generalization).** The deep
input is a **Hecke-stable, full-rank, free ℤ-lattice `Λ` in `S_k(Γ₁N)^∨`** with the Hecke operators
acting by integer matrices; then `heckeAlgℤ ↪ End_ℤ(Λ) ≅ M_r(ℤ)` (Ex 6.5.1) gives `Module.Finite ℤ`.
Refines the existing IHR-a..asm board:

- **IHR-a** `𝕄_k(Γ₁N,ℤ)` integral modular-symbol module, finite free over ℤ (Manin presentation:
  generators `Γ₁N\SL₂ℤ × Sym^{k-2}ℤ²`, 2-/3-term + parabolic relations). *Combinatorial, large.*
  mathlib lacks modular symbols. **Research leaf.** (DS does weight-2 `H₁(X₁N,ℤ)` topologically,
  `ds.txt:16542-16562`; weight-k needs the `Sym^{k-2}` coefficient system — beyond DS.)
- **IHR-b** integer (Heilbronn) Hecke action on `𝕄_k(Γ₁N,ℤ)`. Combinatorial. Depends IHR-a.
- **IHR-c** period pairing `⟨f,{α,β}⊗P⟩=∫_α^β f(z)P(z,1)dz`: convergence (cusp decay), Γ-descent,
  Hecke-equivariance. **The analytic input.** Depends IHR-a.
- **IHR-d** injectivity `S_k ↪ 𝕄_k^∨⊗ℂ` (easy half of Eichler–Shimura: zero periods ⟹ zero form).
  Depends IHR-c.
- **IHR-asm** assemble: `heckeAlgℤ ↪ End_ℤ(𝕄_k^∨_tf)` (Hecke-equivariance + injectivity) ⟹
  `Module.Finite ℤ (heckeAlgℤ)` = **T002 / L0**. The ONLY bounded leaf here (Ex 6.5.1 linear algebra
  + `Module.Finite` of a sub-ℤ-module of a finite free module). Depends IHR-a/b/c/d.

**Why not weight-2-only (DS's literal theorem):** the codebase `Newform N k` is general weight k, so
the DS weight-2 homology does not suffice; the `Sym^{k-2}` modular-symbol generalization (IHR-a) is
required. This is flagged as a genuine source gap beyond DS (cite Shimura Ch. 8 / Hida for weight-k).

**Note (alternative reduction of L0 that stays bounded):** `End_ℤ(Λ)≅M_r(ℤ)` + "sub-ℤ-module of a
finite free ℤ-module is finite" (ℤ Noetherian) means **IHR-asm itself is bounded once `Λ` exists**.
So the entire research-scale content is the *existence* of the Hecke-stable full-rank ℤ-lattice `Λ`
(IHR-a + IHR-c + IHR-d). If one is willing to take *that single existence statement* as the isolated
axiom-like input, IHR-asm + Tranche 1 are all formalizable — i.e. the project can reach "T004/T005
proven modulo one clean lattice-existence hypothesis."

---

## Recommendation
1. **Do Tranche 1 now** (`/beastmode`): isolate `heckeAlgℤ_finite` (L0) as the single FIH instance
   (sorry, = T002), prove L1–L4, rewire the two `NewformOrbit` sorries. Net: 2 deep isolated sorries
   (`coeffSeq_isIntegral`, `coeffField` finite) collapse to **1** (`heckeAlgℤ_finite`) + proven
   derivations. Source-faithful, gate-passing.
2. **Tranche 2 stays a roadmap.** Optionally tighten L0's interface to the *lattice-existence*
   statement (the genuine single deep input) so IHR-asm becomes bounded too.
