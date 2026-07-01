# Decomposition — Integral modular-symbol / Eichler–Shimura substrate (IHR)

*Author: agent, 2026-06-22. Working dir `/Users/mcu22seu/Documents/GitHub/AINTLIB`,
branch `dev/leanmodularforms`, target `LeanModularForms`, mathlib v4.31.0-rc2.*

**Planning artefact only — no proofs.** Every leaf below is a Lean-flavoured statement with a
source locator + verbatim quote, the mathlib/project foundation it builds on, a one-line sketch, and
a classification (FOUNDED / API-GAP / ANALYTIC-FRONTIER). A `:= by sorry` skeleton of the main
definitions accompanies this doc (see "Skeleton" at the end / the companion `.lean` file once built).

---

## 0. Goal and the reduction that makes this cheap

We discharge the single deep input

```
exists_HeckeStableLattice (N) [NeZero N] (k : ℤ) : Nonempty (HeckeStableLattice N k)   -- the one `sorry`
```

(`Labels/HeckeFieldArithmetic.lean:164`) which feeds the *already-proven* endgame
`heckeAlgℤ_finite : Module.Finite ℤ (heckeAlgℤ N k)` (`:171`). The expert reply
(`expert-review/2026-06-22/REVIEW_REPLY.md`) establishes that we do **not** need the in-`S_k`
lattice `HeckeStableLattice` (route A's surjective/Hodge half). It suffices to build the **dual**
package and re-run the same `Module.Finite.of_injective` endgame against `𝕄_k(ℤ)^∨` instead of `Λ`:

> FIH follows from (i) `𝕄_k(Γ₁N;ℤ)` finite free over `ℤ`; (ii) Hecke acts on it by integer matrices,
> Hecke-equivariantly; (iii) the period map `ι : S_k → 𝕄_k(ℤ)^∨ ⊗ ℂ` is Hecke-equivariant and
> **injective**. Then `𝕋ℤ ↪ End_ℤ(𝕄_k(ℤ))`, module-finite. No surjectivity, no full Eichler–Shimura
> isomorphism.

This is the route taken below. The tree has **five top leaves** ES-1 … ES-4 + ES-asm.

**Source anchor for the whole substrate.** Shimura, *Introduction to the Arithmetic Theory of
Automorphic Functions*, **Chapter 8 "The cohomology group associated with cusp forms"** (§8.1 p.223,
§8.2 p.230, §8.3 p.236, §8.4 p.239) and **§3.5** (the lattice (3.5.20) p.84, Thm 3.48 p.83, Thm 3.52
p.85). The integral lattice we need is *literally* Shimura's (3.5.20):

> **(3.5.20)** "There is a discrete *Z*-submodule *L* of *S_k(Γ′)* of maximal rank which is stable
> under the [Γ′αΓ′]_k for all α ∈ Δ." (Shimura p.84)

constructed in §8.4 from the integral group cohomology `H¹_P̄(Γ, D)`, `D = Z^{n+1}` a `Γ`-module via
`ρ_n` (`Sym^n`):

> "For example, let *Γ* be a subgroup of *SL₂(Z)* of finite index, and let *D = Z^{n+1}* with *n ≥ 0*.
> Through the representation *ρ_n*, we can regard *D* as a *Γ*-module. … we obtain a lattice *L* of
> *S_{n+2}(Γ)* which is stable under (ΓαΓ)_{n+2} for every *α ∈ M₂(Z) ∩ GL₂⁺(R)*. This proves the
> statement (3.5.20)." (Shimura §8.4, p.240)

The injectivity-only route replaces "lattice in `S_k`" by "`S_k` injects into the dual of the
integral cohomology"; the integral cohomology *is* `𝕄_k(ℤ)`. **Weight convention:** Shimura's
`n = k − 2`, so `Sym^{k-2}` ↔ `ρ_{k-2}` ↔ his `S_{n+2} = S_k`. We require `k ≥ 2`.

---

## 1. Notation map (source ↔ Lean)

| Object | Shimura | this doc / Lean |
|---|---|---|
| coefficient system | `D = Z^{n+1}` via `ρ_n`, `n=k-2` | `Vℤ k := homog. deg `(k-2)` in `ℤ[X,Y]` = `Sym^{k-2}(ℤ²)` |
| coeff over `ℚ`/`ℝ`/`ℂ` | `X = X^Ψ_n` | `Vℚ k`, base change |
| modular symbols | `H¹_P̄(Γ, D)` (= integral cohomology) **dually** `Div⁰(ℙ¹ℚ)⊗V_{k-2}` coinvariants | `𝕄 N k : Type` |
| Manin generators | (8.1.11)+ρ_n basis | `Γ₁N\SL₂ℤ × basis Vℤ` |
| Hecke double coset | `[Γ₁αΓ₂]_k` (8.3.4) | `heckeSymb N k n` |
| period pairing | `𝔡(f)=f⊗[z;1]ⁿ dz`, `φ(f)`=class (8.2.12,8.2.20) | `periodMap N k` |
| the lattice (L) | (3.5.20) / `L=μ(j(H¹_P̄(Γ,D)))` | not needed in `S_k`; dual `𝕄^∨` |

`ℙ¹(ℚ) = Projectivization ℚ (Fin 2 → ℚ)` = the cusps `ℚ ∪ {∞}`; `Div⁰` = degree-0 divisors =
`ker(deg : (ℙ¹ℚ →₀ ℤ) → ℤ)`. The boundary `∂{α,β} = (β) − (α)` lands in `Div⁰` — this is what makes
the period integral path-independent / well-defined on the *quotient*.

---

## ES-1. The modular-symbol module `𝕄_k(Γ₁N;ℤ)` is finite free over ℤ

### Definition (the non-vacuous one, supporting leaves ES-2..ES-4)

```lean
/-- `Sym^{k-2}(R²)` as homogeneous degree-(k-2) polynomials in 2 vars. -/
abbrev SymPow (R) [CommRing R] (m : ℕ) : Submodule R (MvPolynomial (Fin 2) R) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) R m

/-- The SL₂(ℤ)-action on `Sym^{k-2}` by linear substitution `(X,Y) ↦ (aX+bY, cX+dY)`. -/
def symRep (R) [CommRing R] (m : ℕ) : Representation R SL(2,ℤ) (SymPow R m) := sorry   -- API-GAP

/-- Divisors on ℙ¹(ℚ) of degree 0, as an SL₂(ℤ)-representation (permutation action on cusps). -/
abbrev Div0 (R) [CommRing R] : Submodule R (Projectivization ℚ (Fin 2 → ℚ) →₀ R) :=
  LinearMap.ker (Finsupp.linearCombination R (fun _ => (1 : R)))    -- degree map

def div0Rep (R) [CommRing R] : Representation R SL(2,ℤ) (Div0 R) := sorry              -- builds on Projectivization.Action

/-- The integral modular-symbol module: `Γ₁(N)`-coinvariants of `Div⁰(ℙ¹ℚ) ⊗ Sym^{k-2}`. -/
abbrev modSymRep (N : ℕ) [NeZero N] (k : ℤ) (R) [CommRing R] :
    Representation R (Gamma1 N) (Div0 R ⊗[R] SymPow R (k-2).toNat) :=
  ((div0Rep R).tprod (symRep R _)).comp (Gamma1 N).subtype   -- restrict SL₂ℤ-rep to Γ₁N

def 𝕄 (N : ℕ) [NeZero N] (k : ℤ) (R) [CommRing R] : Type := (modSymRep N k R).Coinvariants
```

* **(a) Lean statement (the leaf):**
  ```lean
  instance : Module.Free ℤ (𝕄 N k ℤ) := sorry
  instance : Module.Finite ℤ (𝕄 N k ℤ) := sorry
  ```
* **(b) Source:** Shimura §8.4 Prop 8.6 (the integral incarnation), and the finite-generation
  mechanism is the homology `H₂(K,X) ≅ X/Y` with `Y = ⟨(α−1)X⟩`:

  > **Prop 8.2** "Let *Y* be the *R*-submodule of *X* generated by *(α−1)X* for all *α ∈ G*. Then
  > *H²_Q̄(K, X)* is isomorphic to *X/Y*." (Shimura p.229)

  i.e. the cuspidal modular-symbol space is a *coinvariants* (= `X/⟨(α−1)X⟩`) — exactly mathlib's
  `Representation.Coinvariants`. Finiteness/finite rank:

  > **Prop 8.6** "The group *Γ* has a finite set of generators, say {σ₁,…,σ_m}. … every element *u*
  > of *Z¹_P̄(Γ, X)* … is completely determined by *u(σ₁),…,u(σ_m)*. This shows that *Z¹_P̄(Γ, D)* …
  > is finitely generated over *Z* …" (Shimura p.239). And **(3.5.20)** asserts the resulting object
  > is a lattice of *maximal rank*.

  The "finitely many Manin symbols" form is **standard (Manin symbols)** — Manin, *Parabolic points
  and zeta functions of modular curves* (1972); Cremona, *Algorithms for Modular Elliptic Curves*,
  Ch. 2; Stein, *Modular Forms: A Computational Approach*, Ch. 8. `[SL₂ℤ : Γ₁N] < ∞` finite × `Sym`
  finite-dim ⟹ finitely many generators.
* **(c) Mathlib foundation:**
  - `Representation.Coinvariants` / `Coinvariants.ker` (`Mathlib/RepresentationTheory/Coinvariants.lean:52,56`)
    — `V_G = V ⧸ ⟨ρ g v − v⟩`. **`instance Module.Finite k (Coinvariants ρ)` for `[Module.Finite k V]`
    is already there** (`:64`). So finiteness of `𝕄` reduces to finiteness of the *coefficient*
    module `Div0 ℤ ⊗ SymPow ℤ (k-2)` over `ℤ` — but `Div0(ℤ)` is **infinite** (ℙ¹ℚ infinite). The
    finite-generation therefore needs the **Manin reduction**, not the naive instance — see API-GAP.
  - `Representation.ofMulAction k G H` (`Basic.lean:396`) — the permutation rep `H →₀ k` for a
    `G`-action on `H`; `div0Rep` is its degree-0 sub. `Projectivization.Action`
    (`Mathlib/LinearAlgebra/Projectivization/Action.lean:44`, `matrixSpecialLinearGroup_smul_def`)
    gives the `SL₂`-action on ℙ¹.
  - `coinvariantsFinsuppLEquiv ρ α : (ρ.finsupp α)_G ≅ (α →₀ V_G)` (`Coinvariants.lean:236`) and
    `coinvariantsTensorFreeLEquiv` (`:462`) — **the Manin-symbol finiteness engine**: coinvariants of
    an *induced/free* module collapse to finitely many copies of `V_G` indexed by `Γ\(generators)`.
  - `MvPolynomial.homogeneousSubmodule` (`Mathlib/RingTheory/MvPolynomial/Homogeneous.lean:90`) — the
    `Sym^{k-2}` model; finite free over `ℤ` of rank `k-1` (monomial basis `XᵃYᵇ, a+b=k-2`).
  - free-over-ℤ: `Module.free_of_finite_type_torsion_free'` (`Mathlib/LinearAlgebra/FreeModule/PID.lean:386`)
    — finite + torsion-free ⟹ free (ℤ is a PID). `Coinvariants` of a free `ℤ`-module is finite but
    may have torsion; torsion-freeness of `𝕄` is the genuine content (see sketch).
* **(d) Sketch:** Present `𝕄 = (Div⁰⊗Sym)_{Γ₁N}` via the Manin map: pick `Γ₁N\SL₂ℤ` coset reps `gᵢ`
  (finite, `[SL₂ℤ:Γ₁N]<∞`); the symbols `gᵢ·{0,∞}⊗P` (`P` a monomial basis of `Sym`) span by
  `Div⁰`-additivity + `SL₂ℤ = ⟨S,T⟩` continued-fraction reduction. Hence finitely generated over `ℤ`.
  Torsion-free: the period map ES-3 embeds `𝕄^∨⊗ℂ ⊇ image of S_k`; more directly the `ℚ`-version
  `𝕄(ℚ)` is finite-dim, `𝕄(ℤ) → 𝕄(ℚ)` need not be injective, so take `𝕄(ℤ)/torsion` (free over PID)
  — this is harmless because Hecke and the period map factor through `𝕄(ℤ)_free` (periods are
  ℂ-valued, kill torsion). Then `Module.free_of_finite_type_torsion_free'`.
* **Classification:** **API-GAP** — `Representation.Coinvariants` and the `Finsupp`/`Projectivization`
  pieces exist, but (i) `symRep` (the `SL₂` action on `Sym^{k-2}`), (ii) the **Manin finite-generation**
  (`coinvariantsFinsuppLEquiv` applied through `Div⁰` + coset reps) are mathlib-absent and must be
  built. **Scope ≈ 600–1000 LOC.** No deep mathematics, but real API. *This is the largest combinatorial
  leaf.*

> **Adversarial check (non-vacuity).** Is `𝕄 N k ℤ` non-trivial and does it actually carry ES-2/ES-3?
> Yes: `(Div⁰⊗Sym)_{Γ₁N}` is the *standard* weight-`k` modular-symbol space, dual to `H¹_P̄(Γ₁N, Sym)`
> (Shimura §8.4 (8.4.2): `H¹_P̄(Γ,D_R)=H¹_P̄(Γ,D)⊗R`). For `N,k` with `S_k(Γ₁N)≠0` it has the right
> rank (`≥ dim S_k`, in fact `2 dim S_k + (cusp/Eis correction)` over `ℚ` by Shimura (8.2.23)). The
> double-coset action (8.3.4) lands on it (ES-2) and the integration pairing (8.2.12) is defined on it
> because `∂{α,β}∈Div⁰` makes `∫_α^β` well-defined (ES-3). It is *not* vacuous and *does* support 4–6.
> **One caveat to verify during build:** the `Div⁰`-coinvariants model and the `H¹_P̄`-cocycle model
> agree (Shimura works with cocycles; the `Div⁰` "homology" model is the dual — Manin's). They are
> canonically dual finite `ℤ`-modules; ES-3 maps `S_k` into `𝕄^∨⊗ℂ` either way. We pick the homology
> (`Div⁰`) model because (a) `Representation.Coinvariants` *is* `H₀`/homology, a perfect fit, and
> (b) the integration pairing `⟨f, {α,β}⊗P⟩` is literally a pairing against a `Div⁰⊗Sym` element.

### ES-1 finiteness — REFINED PLAN (2026-06-22 reconnaissance; supersedes the (c)/(d) engine choice above)

Two corrections after reading mathlib `Coinvariants.lean` + `Cusps.lean` + `OnePoint/ProjectiveLine.lean`:

**(1) `Module.Free ℤ 𝕄` is NOT needed — drop it (and the torsion-freeness worry in (d)).** The faithfulness
endgame (ES-asm) maps `𝕋ℤ → End_ℤ(𝕄)` (the Hecke action on `𝕄`, ES-2) and uses that `End_ℤ(𝕄)` is
`Module.Finite ℤ` *whenever `𝕄` is `Module.Finite ℤ`* (`ℤ` Noetherian ⟹ `Hom(𝕄,𝕄)` f.g.), then `𝕋ℤ ↪
End_ℤ(𝕄)` finite ⟹ `𝕋ℤ` finite. Injectivity of that map comes from ES-3+ES-4 (period map intertwines the
two Hecke actions; `T=0` on `𝕄` ⟹ `T·ι=ι(T·)=0` ⟹ `Tf=0` by ES-4 ⟹ `T=0` on `S_k` ⟹ `T=0` in `𝕋ℤ`).
**`𝕄` may have torsion and it is harmless.** So ES-1 proves only `Module.Finite ℤ (𝕄 N k)`. The skeleton's
`instFree_𝕄` is removed.

**(2) The finiteness engine is NOT `coinvariantsTensorFreeLEquiv`** (that is for *free/regular* reps; `Div⁰`
is the augmentation kernel of a *permutation* rep, not free). Instead an **elementary, fully-founded
(i)+(ii)+(iii) route**, no group homology / no abstract untwisting iso:

- **(i) `Div0 ℤ` is finitely generated over `ℤ[Γ₁N]`** (`MonoidAlgebra ℤ (Gamma1 N)`, via `Representation.asModule` of `div0Rep.comp subtype`).
  - *Finitely many cusps:* `SL(2,ℤ)` acts **transitively** on `ℙ¹ℚ` — `OnePoint.exists_mem_SL2` (`Cusps.lean:33`, the `A=ℤ,K=ℚ` PID case) transported to `Projectivization ℚ (Fin 2→ℚ)` via the action-compatible `OnePoint.equivProjectivization` (`ProjectiveLine.lean:84`; intertwiner `equivProjectivization_smul:130`, `∞ ↦ mk ![1,0]:105`). Then `Γ₁N`-orbits on `ℙ¹ℚ ≅ Γ₁N\SL₂ℤ/Stab(∞)`, a quotient of the **finite** `Γ₁N\SL₂ℤ` (`instFiniteIndexGamma1`). ⟹ `ℤ[ℙ¹ℚ]` f.g. over `ℤ[Γ₁N]` (orbit reps `c₁..c_h`).
  - *Augmentation kernel:* `Div0 = ker(aug)` is generated over `ℤ[Γ₁N]` by `{(s−1)·cᵢ : s ∈ gen set of Γ₁N, i}` ∪ `{cᵢ − c₁ : i≥2}` — **finite, using `Group.FG (Gamma1 N)`** (ES-1b: `Group.FG SL(2,ℤ)` + Schreier `fg_of_index_ne_zero`).
- **(ii) `Div0 ℤ ⊗[ℤ] SymPow ℤ m` (diagonal `Γ₁N`-action) is f.g. over `ℤ[Γ₁N]`**, generated by `{dᵢ ⊗ xⱼ}` (`dᵢ` = the (i) generators, `xⱼ` = monomial ℤ-basis of `SymPow`). *Elementary:* for any `gₖ`, `gₖdᵢ ⊗ xⱼ = gₖ·(dᵢ ⊗ gₖ⁻¹xⱼ)` and `gₖ⁻¹xⱼ ∈ SymPow` (Sym is `Γ`-stable, f.g./ℤ) `= Σ cₘ xₘ`, so every `gₖdᵢ⊗xⱼ ∈ ℤ[Γ]`-span`{dᵢ⊗xⱼ}`. (No abstract `k[G]⊗W≅free` iso required.)
- **(iii) `Coinvariants ρ` of a `ℤ[Γ]`-f.g. module is `Module.Finite ℤ`.** *Elementary:* `Coinvariants.mk` is surjective and `mk (ρ g v) = mk v` (the defining relation, `Coinvariants.mk_inv_tmul`-style), so if `{ρ(g)·tₚ : g∈Γ}` ℤ-spans `V` for finite `{tₚ}`, then `{mk tₚ}` ℤ-spans `Coinvariants` ⟹ finite. (mathlib's `Coinvariants.lean:64` `Module.Finite` instance is only the `Module.Finite ℤ V` case, which fails here since `Div0` is ℤ-infinite — this (iii) is the general `ℤ[Γ]`-f.g. version, to be built.)

**NB — a tempting shortcut that is INVALID (do not attempt).** One might hope to skip (i)/(ii) by working
directly in the quotient: `𝕄 = span{mk((x−y)⊗P)}`, split into `mk(x⊗P) − mk(y⊗P)`, then absorb `g` from
`x = g·cᵢ` via coinvariance `mk((g cᵢ)⊗P) = mk(cᵢ⊗g⁻¹P)` to land in the finite `span{mk(cᵢ⊗monomial)}`. This
is **ill-typed**: a single point `x` has augmentation `1`, so `single x 1 ∉ Div0` and `single x 1 ⊗ P ∉
Div0⊗Sym` — `mk(x⊗P)` is not an element of `𝕄`. The difference `(x)−(y)` cannot have *both* endpoints reduced
to cusp reps by one group element (that is precisely the content of the Manin 2-/3-term relations). So the
augmentation telescoping in (i) is genuinely required; there is no quotient-side shortcut. (Telescoping
formalization: `(g·c₁ − c₁) ∈ ℤ[Γ]`-span`{(sₖ−1)c₁}` for all `g ∈ Γ₁N`, by `Subgroup.closure_induction` over
the `Group.FG (Gamma1 N)` generating set — the property is closed under `*` and `⁻¹`.)

Build as sub-leaves **ES-1c** (i)+(ii) [`Div⁰⊗Sym` f.g. over `ℤ[Γ₁N]`; needs ES-1b] and **ES-1d** (iii) [the
general coinvariants-finiteness lemma; reusable], assembled into `instance : Module.Finite ℤ (𝕄 N k)`.
Prereqs all confirmed present: transitivity, finite index, Schreier — only `Group.FG SL(2,ℤ)` (ES-1b) and the
two elementary spanning lemmas are new.

---

## ES-2. Integer Hecke action on `𝕄_k(ℤ)`, Hecke-equivariant

* **(a) Lean statement:**
  ```lean
  /-- `T_n` (and `U_p` at `p∣N`, `⟨d⟩`) on `𝕄_k(ℤ)` by the Heilbronn matrices, as a ℤ-linear map. -/
  def heckeSymb (N : ℕ) [NeZero N] (k : ℤ) (n : ℕ) : 𝕄 N k ℤ →ₗ[ℤ] 𝕄 N k ℤ := sorry
  def diamondSymb (N : ℕ) [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) : 𝕄 N k ℤ →ₗ[ℤ] 𝕄 N k ℤ := sorry
  -- equivariance with the analytic Hecke operator is stated in ES-3 (`periodMap_hecke`).
  ```
* **(b) Source:** Shimura §8.3, the double-coset action on cohomology, made explicit:

  > "we can define a *C*-linear map *[Γ₁αΓ₂]_{k,Ψ}* of *S_k(Γ₁, Ψ)* to *S_k(Γ₂, Ψ)* by
  > *f | [Γ₁αΓ₂]_{k,Ψ} = det(α)^{k−1} Σᵢ Ψ(αᵢ)f(αᵢ(z))j(αᵢ,z)^{−k}* … moreover we have
  > *𝔡(f | [Γ₁αΓ₂]_{k,Ψ}) = Σᵢ χ(αᵢ)𝔡(f)∘αᵢ*." (Shimura (8.3.4),(8.3.5), p.237)

  > **Prop 8.5** "The diagram [period map commutes with the double-coset actions on `S_k` and on
  > `H¹_P̄`]." (Shimura p.237, completed p.238)

  The integral/combinatorial action via *Heilbronn matrices* is **standard (Manin symbols)**:
  Merel, *Universal Fourier expansions of modular forms* (Heilbronn matrices); Cremona Ch. 2 §2.4;
  Stein Ch. 8. `T_p · {α,β}⊗P = Σ_{Heilbronn h of det p} {hα,hβ}⊗(h·P)`.
* **(c) Mathlib foundation:** `Coinvariants.lift`/`map` (`Coinvariants.lean:105`, and the functoriality
  `Coinvariants.map` of a `G`-equivariant map) — a Hecke operator is induced on coinvariants from the
  finite Heilbronn sum on `Div⁰⊗Sym`. The *integrality* is free (Heilbronn matrices are integer
  matrices acting on the `ℤ`-lattice `Sym^{k-2}(ℤ²)` and permuting `ℙ¹ℚ`). **No mathlib decl for
  Heilbronn matrices** — API-GAP. The project already has the *analytic* `heckeT_n_cusp`
  (`HeckeRIngs/GL2/AdjointTheory.lean:199`) and the **integer Fourier formula** to match against
  (ES-3): `fourierCoeff_heckeT_n_period_one` (`FourierHecke.lean:702`),
  `a_m(T_n f) = Σ_{d|gcd(m,n)} d^{k-1}χ(d) a_{mn/d²}(f)`.
* **(d) Sketch:** Define the Heilbronn finite set `𝓗_p ⊆ M₂(ℤ)` (det `p`); `T_p` on `Div⁰⊗Sym` =
  `Σ_{h∈𝓗_p} (h on cusps) ⊗ (ρ_{k-2}(h) on Sym)`; check it preserves `Coinvariants.ker` (commutes with
  the `Γ₁N`-action up to the coset relabelling, the well-definedness in §8.3 (8.3.3)) ⟹ descends to
  `𝕄`. Integrality automatic. Compose for `T_n` via `T_p`-recursion (project already has the recursion
  shape in `FourierHecke.lean`). `⟨d⟩` = action of a `Γ₀(N)`-rep of `d`.
* **Classification:** **API-GAP** (combinatorial). Heilbronn matrices + the well-definedness on
  coinvariants. **Scope ≈ 400–700 LOC.** Equivariance *with the analytic operator* is deferred to
  ES-3 (it is the content that ties this to the project's `heckeAlgℤ`).

---

## ES-3. The period map `ι : S_k → 𝕄_k(ℤ)^∨ ⊗ ℂ`, well-defined, Γ-invariant, Hecke-equivariant

* **(a) Lean statement (split into sub-leaves):**
  ```lean
  /-- The raw integral `∫_α^β f(z) P(z,1) dz` along a geodesic/segment in ℍ̄, `α,β ∈ ℙ¹(ℚ)`,
      `P ∈ Sym^{k-2}`. (`P(z,1)` = evaluate the homogeneous poly at `(z,1)`.) -/
  def periodIntegral (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
      (α β : Projectivization ℚ (Fin 2 → ℚ)) (P : SymPow ℂ (k-2).toNat) : ℂ := sorry

  -- ES-3a convergence: the integral exists (improper at the cusps α,β) via cusp decay.
  theorem periodIntegral_integrable (f) (α β) (P) : True := sorry      -- "the integral converges"

  -- ES-3b the pairing on the coefficient module `Div⁰⊗Sym` is `Γ₁N`-invariant ⟹ descends to 𝕄.
  def periodMap (N) [NeZero N] (k : ℤ) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] (𝕄 N k ℤ →ₗ[ℤ] ℂ) ⊗[ℤ] ℂ := sorry  -- via Coinvariants.lift

  -- ES-3c Hecke-equivariance: `ι (T_n f) = (heckeSymb n)^∨ (ι f)`.
  theorem periodMap_hecke (N) [NeZero N] (k) (n : ℕ) (f) :
      periodMap N k (heckeEnd N k ⟨n,_⟩ f) = (dualMap (heckeSymb N k n)) (periodMap N k f) := sorry
  ```
* **(b) Source:** Shimura §8.2 — the holomorphic vector differential and the cocycle:

  > "First we define, for every *f ∈ S_{n+2}(Γ, Ψ)*, a holomorphic vector differential form *𝔡(f)*
  > with values in *C^r ⊗ C^{n+1}* by *𝔡(f) = f ⊗ [z;1]ⁿ dz*." (Shimura (8.2.12), p.232)

  > "Fix any point *z₀* of 𝔥. For *f ∈ S_{n+2}(Γ, Ψ)*, put *F(z) = ∫_{z₀}^z 𝔡(f) + v* … Since *𝔡(f)*
  > is holomorphic, *F(z)* is independent of the choice of the path of integral. For every *α ∈ Γ* …
  > *t(αβ) = t(α) + χ(α)t(β)*, so that *t ∈ Z¹(Γ, X_c)*." (Shimura p.233)

  Convergence at cusps (the only delicate point):

  > "Since *p(w)* is a polynomial in *w*, and *Φ(0) = 0*, the integral has a limit when *ρ(z)* tends
  > to ∞, i.e., *z* tends to *s* (with respect to the topology of 𝔥*). Therefore we can meaningfully
  > put *F(s) = lim_{z→s} F(z)*." (Shimura p.233) — `Φ(0)=0` is exactly the cusp form's vanishing
  > constant term; the polynomial weight `P(z,1)` is dominated by the exponential `q`-decay.

  Equivariance is Shimura Prop 8.5 + (8.3.5) (cited under ES-2). The pairing form (the bilinear `A`):

  > "Therefore we can define an *R*-valued *R*-bilinear form *A(f, g)* on *S_{n+2}(Γ, Ψ)* by
  > *A(f, g) = ∫_{Γ\𝔥} ᵗRe(𝔡(f)) ∧ W·Re(𝔡(g))*." (Shimura (8.2.17), p.232)
* **(c) Mathlib / project foundation — STRONG:**
  - **Convergence (ES-3a):** `CuspFormClass.exp_decay_atImInfty`
    (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:413`, and the `IsZeroAtImInfty` version `:350`):
    `f =O[atImInfty] (τ ↦ exp(−2π·τ.im/h))`. The polynomial `P(z,1)` is `O(z^{k-2})`, beaten by the
    exponential ⟹ `∫` converges at the cusp. `ModularForm.qExpansion_coeff_eq_intervalIntegral`
    (`QExpansion.lean:295`/`359`) shows mathlib *already* integrates a form along a horizontal segment
    `∫ u in 0..h, … f⟨u+t·I,…⟩` — the period integral is the same kind of object.
  - **Integrability machinery:** the project's Petersson construction
    (`Modularforms/PeterssonInnerProduct.lean`, `PeterssonLevelN.lean`) already builds set-integrals of
    forms over ℍ with `MeasureTheory`/`intervalIntegral`/`IntegrableOn`; `ResToImagAxis`
    (`Modularforms/ResToImagAxis.lean`) integrates a form along the imaginary axis (the prototype
    geodesic `{0,∞}`). These are directly reusable for `periodIntegral`.
  - **Descent (ES-3b):** `Representation.Coinvariants.lift f h` (`Coinvariants.lean:105`): a
    `Γ₁N`-invariant linear functional on `Div⁰⊗Sym` induces a functional on `𝕄`. The invariance is
    Shimura (8.2.15)/(8.2.16) (`𝔡(f)∘α = χ(α)𝔡(f)`) = the slash-invariance of `f`, which the project
    has (`CuspForm` is `SlashInvariantForm`-based).
  - **Equivariance (ES-3c):** matches the integer Fourier formula `fourierCoeff_heckeT_n_period_one`
    (`FourierHecke.lean:702`) against the Heilbronn action — the analytic `heckeEnd`
    (`HeckeFieldArithmetic.lean:35`) ↔ combinatorial `heckeSymb`.
* **(d) Sketch:** `periodIntegral f α β P` := integral of `f(z)·P(z,1)` along the hyperbolic geodesic
  from `α` to `β`; reduce to base case `{0,∞}` along imaginary axis (move by `SL₂ℤ`), split off the
  cusp neighbourhoods, bound by `exp_decay × poly` ⟹ converges (ES-3a). Bilinear & `Γ₁N`-invariant in
  the `Div⁰⊗Sym` slot (boundary `(β)−(α)∈Div⁰`, slash invariance) ⟹ `Coinvariants.lift` to a
  functional on `𝕄`; tensor with ℂ ⟹ `periodMap` (ES-3b). Equivariance by the matching of the two
  Hecke descriptions (ES-3c).
* **Classification:** **ANALYTIC-FRONTIER (but well-founded)**. The convergence ingredient
  (`exp_decay_atImInfty`) and the integration substrate (`qExpansion_coeff_eq_intervalIntegral`,
  Petersson integrals) **exist in mathlib/project** — this is the decisive de-risking find. The work
  is: define the geodesic period integral, prove convergence from decay, prove `Γ`-invariance, prove
  Hecke-equivariance. **Scope ≈ 800–1500 LOC.** Higher risk than ES-1/2 but *not* missing foundations.

---

## ES-4. Injectivity of `ι` — "a nonzero cusp form has a nonzero period" (the genuine core)

* **(a) Lean statement:**
  ```lean
  theorem periodMap_injective (N) [NeZero N] (k : ℤ) (hk : 2 ≤ k) :
      Function.Injective (periodMap N k) := sorry
  ```
* **(b) Source — Shimura's proof is short and uses the Petersson pairing:**

  > "Now suppose that *φ(f) = 0*. Then, choosing the constant vector *a* of (8.2.19) suitably, we may
  > put *u = 0*. Then (8.2.22) implies *A(f, g) = 0* for every *g ∈ S_{n+2}(Γ, Ψ)*. Since *A(f, g)* is
  > non-degenerate, *f* must be 0. This proves that the map *φ* is injective." (Shimura p.235)

  Non-degeneracy of `A` reduces to the Petersson inner product:

  > "*A(f, iⁿ⁻¹g) = 2ⁿ · Re((f, g))*. … Therefore, *A(f, g)* is non-degenerate." (Shimura (8.2.18c),
  > p.232) — here `(f,g)` is the (positive-definite) Petersson inner product.
* **(c) Mathlib / project foundation — TWO independent routes, both founded:**

  **Route ES-4/Petersson (Shimura's own):** non-degeneracy of `A` ⟸ positive-definiteness of the
  Petersson product, **already proven in the project**:
  - `CuspForm.pet_definite` (`Modularforms/PeterssonInner.lean:66`): `pet f f = 0 → f = 0`.
  - `petN_definite` (`Modularforms/PeterssonLevelN.lean:147`): positive-definiteness at level `N`.
  So: `ι f = 0` ⟹ (the real-cohomology class `u=0`) ⟹ `A(f,g)=0 ∀g` ⟹ `Re(f,f)=0` ⟹ `pet f f=0` ⟹
  `f=0`. The missing glue is the identity `A(f, iⁿ⁻¹g) = 2ⁿ Re(f,g)` (8.2.18c) relating the
  cohomological pairing to Petersson — a Stokes/Green's-theorem computation over the fundamental
  domain (8.2.22), which uses the project's fundamental-domain & Petersson integral machinery.
  - **★ Stokes foundation CONFIRMED PRESENT in mathlib (2026-06-22, full-build de-risking):** the
    period↔Petersson identity's analytic engine — the 2D Green's/divergence theorem — exists as
    `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt_off_countable`
    (`Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:504`; also box versions `:267`/`:428`), plus
    `Analysis/Complex/CauchyIntegral.lean` (Cauchy = Green's for holomorphic) and
    `MeasureTheory/Integral/CurveIntegral/Poincare.lean` (curve integrals of closed 1-forms / Poincaré).
    ES-4 is NOT blocked by a missing Stokes theorem. The real work is applying it to the *non-rectangular*
    Γ-fundamental domain — likely via the closed-1-form/`Poincare` route (period pairing = integral of a
    closed form over the boundary cycle) or box-approximation of the FD. Deepest leaf, but founded.

  **Route ES-4/qExpansion (more elementary, mathlib-native — recommended first):** A *finite* subset of
  the period values already recovers the Fourier coefficients, and a cusp form is determined by its
  `q`-expansion:
  - `ModularForm.qExpansion_coeff_eq_intervalIntegral` (`QExpansion.lean:295`,`359`):
    `(qExpansion h f).coeff n = (1/h)∫ u in 0..h, q^{-n}·f(u+t·I)` — each Fourier coefficient is a
    **horizontal-segment period** of `f`. The horizontal segment `[t·I, h+t·I]` is the symbol
    `{t·I, h+t·I}` (a `Γ∞`-translate path), and integrating `f·z^j` packages all coefficients.
  - `CuspFormClass.qExpansion_eq_zero_iff` (`QExpansion.lean:590`, and `:506`):
    `qExpansion h f = 0 ↔ f = 0`.
  So: if *all* periods of `f` vanish (in particular all the horizontal `q^{-n}`-weighted ones), then
  every `qExpansion`-coefficient vanishes, hence `qExpansion f = 0`, hence `f = 0`. This bypasses the
  Stokes identity entirely. **Caveat to verify:** the horizontal-segment integral `∫ q^{-n} f` uses the
  weight `q^{-n}=exp(-2πin z/h)`, which is *not* a polynomial `P(z,1)∈Sym^{k-2}`; so this exact
  functional is not literally a `𝕄`-pairing unless we either (i) enlarge the test functions, or (ii)
  observe that the `𝕄`-periods over the `Γ`-orbit of `{0,∞}` plus the cusp expansions still separate
  forms. The clean statement to verify: *the period functionals over `{cusps}×Sym^{k-2}` separate
  `S_k`* — which is exactly Shimura's injectivity, so for a fully rigorous ES-4 we likely still route
  through the pairing `A` (Route 1). **Route 2 is the sanity check / fallback and may suffice if the
  set of `𝕄`-symbols is taken large enough (all of `Div⁰`, not just `{0,∞}`).**
* **(d) Sketch (Route 1, the faithful one):** `ι f = 0` ⟹ choose representing cocycle `u=0` (8.2.19)
  ⟹ Stokes over the fundamental domain (8.2.22): `A(f,g)=Σ ᵗu(σ⁻¹)W ∫ dg = 0`. Take `g = iⁿ⁻¹·`(scaled
  `f`); (8.2.18c) gives `A(f, iⁿ⁻¹f)=2ⁿ Re(f,f) = 2ⁿ·petN f f`; `petN_definite` ⟹ `f=0`.
* **Classification:** **ANALYTIC-FRONTIER** — the genuine core. **But** it is *well-founded*: the
  positive-definiteness (`petN_definite`) and the `q`-expansion faithfulness (`qExpansion_eq_zero_iff`)
  are **already available**; the residual is the Stokes/Green identity (8.2.18c/8.2.22) tying the
  cohomological pairing to Petersson, or (Route 2) showing the symbol set separates `S_k`.
  **Scope ≈ 800–1800 LOC** depending on route. This is the highest-risk leaf; recommend prototyping
  Route 2 (mathlib-native) to validate the architecture before committing to Route 1's Stokes work.

---

## ES-asm. Assemble FIH from ES-1/2/4 (the dual-lattice endgame)

* **(a) Lean statement:**
  ```lean
  -- replaces `exists_HeckeStableLattice`; feeds `heckeAlgℤ_finite` unchanged in spirit.
  instance heckeAlgℤ_finite' (N) [NeZero N] (k : ℤ) : Module.Finite ℤ (heckeAlgℤ N k) := sorry
  ```
* **(b) Source / logic:** the expert reply's Q2 faithfulness argument (verbatim,
  `REVIEW_REPLY.md`):

  > "if *T ∈ 𝕋ℤ* acts as 0 on *𝕄_k(ℤ)*, then *T = 0* on *𝕄_k(ℤ)^∨⊗ℂ*, so for all *f*,
  > *ι(Tf) = T·ι(f) = 0*, so *Tf ∈ ker ι = 0*, so *T = 0* on *S_k*, so *T = 0* … Hence
  > *𝕋ℤ ↪ End_ℤ(𝕄_k(ℤ)) ≅ M_r(ℤ)*, module-finite."

  Algebraically identical to Shimura Thm 3.48(3) / the project's existing `heckeAlgℤ_finite`.
* **(c) Foundation:** `Module.Finite.of_injective` + `LinearMap.restrict` — **exactly the proof already
  in `HeckeFieldArithmetic.lean:171–186`**, with `H.toSubmodule` (the in-`S_k` lattice) replaced by
  `𝕄 N k ℤ` and the faithfulness coming from ES-2 (integer action) + ES-4 (`ι` injective &
  Hecke-equivariant) instead of from `spanning`. The map is `Φ : heckeAlgℤ → End_ℤ(𝕄_k(ℤ))`,
  `T ↦ heckeSymb`-action of `T`; injective because `ι` is injective & equivariant.
* **(d) Sketch:** Build `Φ : heckeAlgℤ N k →ₗ[ℤ] (𝕄 N k ℤ →ₗ[ℤ] 𝕄 N k ℤ)` sending each generator `Tₙ,⟨d⟩`
  to `heckeSymb/diamondSymb` (ES-2), extend by `Algebra.adjoin_induction`. Injective: `Φ T = 0` ⟹ `T`
  kills `𝕄(ℤ)` ⟹ kills `𝕄^∨⊗ℂ` ⟹ (ES-3c equivariance) `ι(T·f)=0 ∀f` ⟹ (ES-4) `T·f=0 ∀f` ⟹ `T=0` in
  `End_ℂ(S_k)`. Then `End_ℤ(𝕄(ℤ))` finite (ES-1 free f.g.) ⟹ `Module.Finite.of_injective Φ`.
* **Classification:** **FOUNDED** — a near-verbatim re-run of the existing endgame against the dual
  module. **Scope ≈ 150–300 LOC.** *Lowest-risk leaf; do it early as a stub against the ES-1/2/4
  interfaces to lock the contract.*

---

## 2. Feasibility paragraph

**Founded-and-bounded:** **ES-asm** (~200 LOC, a copy of the proven endgame) and the *algebraic core*
of **ES-1** (`Representation.Coinvariants` gives `H₀` and `Module.Finite` for free; `MvPolynomial`
homogeneous gives `Sym`; `Projectivization` + `ofMulAction` give `Div⁰`; PID-freeness lemma gives
"free"). **ES-2** is purely combinatorial (Heilbronn matrices + well-definedness on coinvariants) —
bounded but API-heavy. These three are "engineering": large but de-risked, no missing mathematics.

**Genuinely research-scale (but well-founded, *not* blocked):** **ES-3** (period integral: define the
geodesic integral, prove convergence, `Γ`-invariance, Hecke-equivariance) and **ES-4** (injectivity).
The decisive finding is that **both rest on mathlib/project infrastructure that already exists**:
`CuspFormClass.exp_decay_atImInfty` (convergence), `ModularForm.qExpansion_coeff_eq_intervalIntegral`
(forms integrated along segments = Fourier coefficients), `CuspFormClass.qExpansion_eq_zero_iff`
(a form is its `q`-expansion), and — for Shimura's own injectivity argument — the project's
**already-proven Petersson positive-definiteness** `petN_definite` / `pet_definite`. So ES-4's "analytic
core" is *not* a missing-foundation wall; it is a Stokes/Green computation (8.2.18c/8.2.22) on top of
existing definiteness, with an even-more-elementary `q`-expansion fallback to validate the design.

**Overall verdict:** the substrate is **feasible without inventing new analysis**. Total new code
≈ 3000–5000 LOC across the five leaves. The risk is concentrated in ES-3/ES-4 *engineering* (contour
integrals over geodesics ending at cusps, and the Stokes identity), not in absent prerequisites.

## 3. The deepest API gaps, named precisely

1. **`Sym^{k-2}` as an `SL₂(ℤ)`/`GL₂(ℚ)` representation** (`symRep`). mathlib has the *module*
   (`MvPolynomial.homogeneousSubmodule`) and `SymmetricPower` (`LinearAlgebra/TensorPower/Symmetric.lean`,
   whose own TODO lists "Relate to homogeneous polynomials" and gives *no* group action), but **no
   linear `SL₂`-action by substitution** and no `Representation` instance. Must build:
   `(g·P)(X,Y) = P(g⁻¹·(X,Y))` (or `g·` depending on the slash convention), prove it's a `MonoidHom`
   into `End`. Cleanest on the `MvPolynomial` model. ~150–300 LOC. **(Prerequisite of ES-1/2/3.)**
2. **Manin finite-generation of the coinvariants** — `(Div⁰(ℙ¹ℚ)⊗Sym)_{Γ₁N}` is finitely generated
   over `ℤ` *despite* `Div⁰(ℙ¹ℚ)` being infinite. mathlib's `Coinvariants.Module.Finite` instance does
   **not** apply (coefficient module infinite). Need the Manin reduction
   (`coinvariantsFinsuppLEquiv`/`coinvariantsTensorFreeLEquiv` through `Γ₁N\SL₂ℤ` coset reps + the
   `S,T,U` relations). **No mathlib decl.** ~300–500 LOC. **(Heart of ES-1.)**
3. **Heilbronn matrices and the Hecke action on coinvariants** (`heckeSymb`). No mathlib
   `Heilbronn`/modular-symbol-Hecke decl. ~400–700 LOC. **(ES-2.)**
4. **The geodesic period integral with cusp endpoints** (`periodIntegral`) and its **convergence from
   decay**. mathlib has `exp_decay_atImInfty` and segment integrals but **no "integral of a cusp form
   along a hyperbolic geodesic between two cusps" decl**. ~400–800 LOC. **(ES-3.)**
5. **The Eichler–Shimura/Petersson Stokes identity `A(f, iⁿ⁻¹g) = 2ⁿ Re(f,g)`** (8.2.18c) tying the
   cohomological pairing to the Petersson product — needed for the *faithful* injectivity (ES-4 Route 1).
   ~300–600 LOC, on top of the existing fundamental-domain/Petersson machinery.

6. **`Representation.tprod` ↔ `Coinvariants` instance diamond** (newly found while building the
   skeleton — see §5 API-GAP #6). Minor but real: forces the ES-1 build onto the bundled `Rep R G`
   category (`Rep.coinvariantsTensor`) instead of unbundled `Representation.tprod` + `Coinvariants`.
   ~50–150 LOC of bundled-category plumbing.

mathlib has **none** of: modular curves, Eichler–Shimura map, modular/Manin symbols, integral Hecke
algebra, q-expansion principle (confirmed by the brief and by search). This substrate builds the first
four from `Representation.Coinvariants` (bundled `Rep`) + analysis.

## 4. Recommended build order (most-founded first)

1. **ES-asm stub first** (~1 day): write `heckeAlgℤ_finite'` against *opaque* `𝕄`, `heckeSymb`,
   `periodMap`, `periodMap_injective` interfaces (all `sorry`). This *locks the contract* and proves the
   reduction compiles — the cheapest possible validation that leaves 1–4 are sufficient.
2. **API-GAP #1 `symRep`** (the `SL₂`-action on `Sym^{k-2}` via `MvPolynomial`). Self-contained,
   reusable, unblocks everything.
3. **ES-1** (`𝕄` definition via `Coinvariants` + Manin finite-generation #2 + free-over-ℤ). Largest
   combinatorial leaf; deliver `Module.Free`+`Module.Finite ℤ (𝕄 N k ℤ)`.
4. **ES-2** (Heilbronn `heckeSymb`/`diamondSymb`, integrality). Combinatorial, depends on ES-1 + #1.
5. **ES-3** (period integral, convergence via `exp_decay_atImInfty`, descent via `Coinvariants.lift`,
   equivariance via the integer Fourier formula). First analytic leaf.
6. **ES-4** — prototype **Route 2** (`qExpansion_coeff_eq_intervalIntegral` + `qExpansion_eq_zero_iff`)
   to validate, then commit to **Route 1** (Stokes #5 + `petN_definite`) for the faithful statement.
7. **Discharge ES-asm** with the real leaves; delete the `exists_HeckeStableLattice` `sorry`.

---

## 5. Skeleton (`:= by sorry`, typecheck-targeted) — BUILT GREEN

A companion Lean skeleton encoding ES-1…asm against mathlib v4.31 foundations is **written and
compiles** at

```
projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/ModularSymbols/Skeleton.lean
```

**Build status (this session):** `lake build LeanModularForms.HeckeRIngs.GL2.ModularSymbols.Skeleton`
succeeds — **12 `sorry` warnings (one per leaf/instance), zero non-`sorry` diagnostics**. Not imported
by the library aggregator (skeleton only).

**What compiled vs. what is stubbed.** The *intended coefficient representation*
`modSymRep N k R := ((div0Rep R).tprod (symRep R (k-2).toNat)).comp (Γ₁N).subtype`
— i.e. `Div⁰(ℙ¹ℚ) ⊗ Sym^{k-2}` as an `SL₂(ℤ)`-rep restricted to `Γ₁N` — **typechecks** against
`Representation.tprod` + `MvPolynomial.homogeneousSubmodule` + `Projectivization`. So the *shape* of
ES-1's definition is validated. `𝕄 N k` is kept **opaque** (with stated `AddCommGroup`/`Module ℤ`,
`Module.Finite`, `Module.Free` instances) for one concrete reason discovered while building:

> **API-GAP #6 (instance diamond, newly found).** `(modSymRep N k R).Coinvariants` does **not**
> elaborate. `Representation.tprod` types its codomain via `TensorProduct.addCommMonoid` /
> `TensorProduct.instModule`, while `Representation.Coinvariants` requires `[AddCommGroup V]` and is
> stated against `AddCommGroup.toAddCommMonoid`. These instances are propositionally equal but
> syntactically distinct, giving "Application type mismatch: `TensorProduct.addCommMonoid` vs
> `AddCommGroup.toAddCommMonoid`"; `letI` cannot fix it (the representation's type is already fixed).
> **Resolution for the real build:** use the *bundled* category `Rep R (Γ₁N)` and
> `Rep.coinvariantsTensor` (`Coinvariants.lean:32`) rather than the unbundled `Representation.tprod` +
> `Coinvariants`; the bundled objects carry coherent instances, and `coinvariantsTensorFreeLEquiv`
> (`Coinvariants.lean:462`) doubles as the Manin finite-generation engine (API-GAP #2). This adds a
> small amount of bundled-category plumbing to ES-1 but removes the diamond. *Verified live this
> session.*

The load-bearing mathlib citations the skeleton imports/uses, all signature-checked in this session:

- `Representation` (= `G →* (V →ₗ[k] V)`), `Representation.Coinvariants`, `Coinvariants.ker`,
  `Coinvariants.lift`, `Coinvariants.mk`, the `Module.Finite` instance, `coinvariantsFinsuppLEquiv`
  — `Mathlib/RepresentationTheory/{Basic,Coinvariants}.lean`.
- `Representation.ofMulAction`, `Representation.free` — `Mathlib/RepresentationTheory/Basic.lean`.
- `Projectivization`, `MulAction (ℙ K V)`, `matrixSpecialLinearGroup_smul_def`,
  `Projectivization.finite_of_finite` — `Mathlib/LinearAlgebra/Projectivization/{Basic,Action,Cardinality}.lean`.
- `MvPolynomial.homogeneousSubmodule` — `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`.
- `Module.free_of_finite_type_torsion_free'`, `Module.Finite.of_injective`, `LinearMap.restrict` —
  `Mathlib/LinearAlgebra/FreeModule/PID.lean`, `Mathlib/RingTheory/Finiteness/*`.
- `CuspFormClass.exp_decay_atImInfty`, `UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty`,
  `ModularForm.qExpansion_coeff_eq_intervalIntegral`, `qExpansion_coeff_eq_circleIntegral`,
  `CuspFormClass.qExpansion_eq_zero_iff` — `Mathlib/NumberTheory/ModularForms/QExpansion.lean`.

Project foundations it ties into (signature-checked):

- `heckeEnd`, `heckeAlgℤ`, `HeckeStableLattice`, `exists_HeckeStableLattice`, `heckeAlgℤ_finite`
  (the endgame to mirror) — `Labels/HeckeFieldArithmetic.lean`.
- `heckeT_n_cusp` (`HeckeRIngs/GL2/AdjointTheory.lean:199`), the integer Fourier formula
  `fourierCoeff_heckeT_n_period_one` (`HeckeRIngs/GL2/FourierHecke.lean:702`), `diamondOpCusp`
  (`HeckeRIngs/GL2/Gamma1Pair.lean:326`).
- `petN`, `petN_definite` (`Modularforms/PeterssonLevelN.lean:63,147`), `CuspForm.pet_definite`
  (`Modularforms/PeterssonInner.lean:66`), `ResToImagAxis` (`Modularforms/ResToImagAxis.lean`).
