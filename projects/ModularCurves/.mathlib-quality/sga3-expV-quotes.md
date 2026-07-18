# [T-Q2-A711] SGA III, Exposé V — locator + source of record

Read 2026-07-08 by fable-P4 from `refs/ModularCurves/sga3-1.pdf` (landed 2026-07-08 per
v10.27). **Scanned, no text layer** (pdftotext yields only the page-number stamps) — read as
page images. **Offset: printed page = pdf page − 13.**

| what | printed pp. | pdf pp. |
|---|---|---|
| Exposé V, §4 *Passage au quotient par une relation d'équivalence finie et plate* (THÉORÈME 4.1) | ~263–270 | ~276–283 |
| — proof of 4.1 (iii) | 266 | 279 |
| — **proof of 4.1 (iv)** + **LEMME 4.2** | 268 | 281 |
| — Lemme 4.2 proof + the `A₀ ⊗_B A₀ → A₁` bijectivity endgame | 269 | 282 |
| §5 *Passage au quotient … (cas général)* — reduction to `d₁` finite locally free of rank `n` | 267 | 280 |
| §6 (conoyau in annelés) / §7 *Quotient par une prérelation d'équivalence propre et plate* (THM 7.1) | 275–277 | 288–290 |
| Exposé VI_A begins | 287 | 300 |

## Why this is the right citation

KM A7.1.1 (book p. 216) defers its proof to *"(SGA III, Exp V, 4.1)"* — and Exp. V §4's
Théorème 4.1 is about a **finite flat equivalence groupoid** `X₁ ⇉ X₀`, not literally about a
finite group action. The translation is the standard one: a *free* action of a finite group `G`
on `X₀ = Spec A` is the groupoid `X₁ = G × X₀ ⇉ X₀` with `d₀ = pr₂`, `d₁ = action`, and:

* **4.1 (iv)** (printed p. 267, proof on p. 268 = pdf 281): *"Si `(d₀, d₁)` est un couple
  d'équivalence, `X₁ ⟶ X₀ ×_Y X₀` est un isomorphisme et `p` est fidèlement plat."*
  Its proof opens (pdf 281): *"Il suffit de montrer que, pour tout idéal premier `𝔭` de `B`,
  l'homomorphisme `A_{0𝔭} ⊗_{B_𝔭} A_{0𝔭} ⟶ A_{1𝔭}` de composantes `δ_{0𝔭}` et `δ_{1𝔭}` est
  bijectif."* — **this is exactly our `torsorMul_bijective_of_isFreeAlgebraAction`** (with
  `B = Aᴳ`, `A₁ = ∏_G A`, `δ₀ ⊗ δ₁ = torsorMul`).

* The proof's ingredients, in order (pdf 281–282):
  1. **Localize at a prime `𝔭` of `B`** ⟹ may assume `B` local; then `A_{0𝔭}` is **semi-local**
     (*"si `𝔪` est un idéal maximal de `A_{0𝔭}`, les autres idéaux maximaux sont de la forme
     `δ₁⁻¹(𝔫)` … l'assertion résulte donc de ce qu'il y a au plus `n = [A₁ : A₀]` idéaux
     premiers `𝔫`"*).
  2. **Faithfully flat base change to make the residue field of `B` infinite**
     (*"Quitte à faire un changement de base fidèlement plat, on peut aussi supposer que le
     corps résiduel de `B` est infini"*).
  3. **LEMME 4.2** (printed p. 268 = pdf 281–282), verbatim:
     > "Soient `B` un anneau local de corps résiduel infini, `A` un anneau semi-local et
     > `i : B ⟶ A` un homomorphisme qui envoie l'idéal maximal `𝔫` de `B` dans le radical `𝔯`
     > de `A`. Soient `M` un `A`-module libre de rang `n` et `N` un `B`-sous-module de `M` qui
     > engendre `M` en tant que `A`-module. Alors `N` contient une base de `M` sur `A`."
     (Proof = Nakayama: reduce to `M/𝔯M` over `A/𝔯 = K₁ × ⋯ × K_r`, then a linear-combination /
     induction argument.)
  4. **Assembly** (pdf 282): apply 4.2 with `B = B`, `A = A₀`, `M = A₁` (an `A₀`-module via
     `δ₁`), `N = δ₀(A₀)` — `N` generates because `d₀ ⊠ d₁` is a monomorphism, hence
     `A₀ ⊗_B A₀ ⟶ A₁` is surjective. A basis `a₁,…,a_n` of `A₁` over `A₀` (as `δ₀(aᵢ)`) is then
     shown to be a `B`-basis of `A₀`, whence `A₀ ⊗_B A₀ ⟶ A₁` carries a basis to a basis and is
     **bijective**.

* **§5** (pdf 280) records the reduction that makes "finite flat" usable: *"on est ramené au cas
  où `d₁` est fini localement libre de rang `n`"* — `X₀ = ∐ U^{(n)}` over the ranks. For a free
  finite group action this is where KM's *"in the absence of noetherian hypotheses, this is
  rather delicate"* bites: finiteness of `A` over `Aᴳ` is *not* a hypothesis of KM A7.1.1, it
  has to come from the freeness + the finite group (integrality of `A` over `Aᴳ` is automatic;
  *finite locally free of rank `|G|`* is the content).

## Consequence for the Lean plan (T-Q2-A711)

Route **(β)** (prove it ourselves) is now source-anchored end-to-end — no memory-sourced maths.
The formalization decomposes exactly along SGA's proof; see the board for leaves
**A711-L1 … A711-L4**. `chr_of_isFreeAlgebraAction` (landed, axiom-clean) is the input that
makes step 1's semi-local analysis apply at every prime.

Chase–Harrison–Rosenberg remains an *optional* acquisition (v10.27): it packages the same
content as "`A/Aᴳ` is a Galois extension with group `G`" and would let us cite a single
equivalence instead of reconstructing steps 1–4.
