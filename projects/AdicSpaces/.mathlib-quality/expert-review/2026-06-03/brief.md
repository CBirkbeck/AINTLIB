# Review brief — Formalisation of Wedhorn's Theorem 8.28(b) (Tate acyclicity / the structure sheaf on an adic spectrum)

*Prepared 2026-06-03 for an expert in adic spaces and Huber theory. Self-contained: no repository access required. The formalisation is in Lean 4 on top of Mathlib; this brief contains no code and no file references — only mathematics.*

> *Note for a reviewer who saw our earlier (2026-05-31) brief:* that brief asked how to avoid formalising the full Henkel–Bourbaki open mapping theorem behind Wedhorn's "Proof: Missing" Propositions 6.17/6.18. **That gap is now closed** — we formalised the open mapping theorem (no σ-compactness) and 6.17/6.18 sorry-free (Theorem 5.1 below). The genuine remaining blocker has moved downstream to **Proposition 7.48** (`Spa Â ≅ Spa A`), which is the focus of §8.1 and the questions in §9.

---

## 1. Goal

We are formalising **Wedhorn, *Adic Spaces*, Theorem 8.28(b)**: for an affinoid ring `A = (A, A⁺)` that is a **strongly noetherian Tate ring**, with `X = Spa A`, the structure presheaf `𝒪_X` is a **sheaf of complete topological rings**, and moreover `Hq(U, 𝒪_X) = 0` for every `q ≥ 1` and every rational subset `U ⊆ X`.

Concretely the deliverable is one theorem — the **sheafy theorem** — asserting `𝒪_X` is sheafy, where "sheafy" is packaged (faithfully to Wedhorn's Remark 8.20) as the conjunction of two conditions on every finite rational covering `(Uᵢ)` of every rational `U`:

- **(embedding)** the canonical map `𝒪_X(U) → ∏ᵢ 𝒪_X(Uᵢ)` is a *topological embedding* (injective, and a homeomorphism onto its image with the subspace topology of the product); and
- **(gluing)** every family of sections agreeing on overlaps amalgamates to a global section.

This brief asks for **strategic guidance on whether our overall route to the sheafy theorem is sound**, with particular focus on one foundational input (Proposition 7.48 below) that we believe is the single genuinely-deep external dependency.

---

## 2. Background and references

### 2.1. Setting and conventions

We follow Wedhorn's notation throughout.

- `A = (A, A⁺)` is an **affinoid ring**: `A` a (to-be-)complete topological ring of f-adic type and `A⁺ ⊆ A` an open integrally-closed subring of power-bounded elements. We are in the **Tate** case: `A` contains a topologically nilpotent unit `ϖ` (a *pseudo-uniformiser*). A **ring of definition** `A₀ ⊆ A` is an open subring carrying the `ϖ·A₀`-adic topology.
- `Spa A = { v ∈ Spv A : v continuous, v(f) ≤ 1 for all f ∈ A⁺ }` is the **adic spectrum**, a spectral space; points are equivalence classes of continuous valuations. For finite `T ⊆ A` with `T·A` open and `s ∈ T`, the **rational subset** `R(T/s) = { x : x(t) ≤ x(s) ≠ 0, t ∈ T }`. Rational subsets form a basis of `X` stable under finite intersection.
- The **structure presheaf** `𝒪_X`: on a rational subset `U = R(T/s)`, `𝒪_X(U)` is the *completion* of the localisation `A[T/s]` for the natural ring topology making `T/s` power-bounded. It is again a complete Tate ring; restriction maps are the induced continuous ring homomorphisms. (In the formalisation this completed-localisation value is the object we call the *presheaf value at `U`*; we write `𝒪_X(U)` here.)
- **Strongly noetherian** (Wedhorn Prop.+Def. 6.36): a Tate ring `A` is *strongly noetherian* iff the completed power-series Tate algebra `Â⟨X₁,…,Xₙ⟩` is noetherian for every `n ≥ 0`; equivalently every Tate ring topologically of finite type (t.f.t.) over `A` is noetherian. The case `n = 0` gives: strongly noetherian + complete ⟹ `A` itself noetherian.
- **Topologically of finite type (t.f.t.)** is Wedhorn §6.6's notion: an adic morphism with a dense finitely-generated subalgebra over a ring of definition.

A central structural fact: `𝒪_X` is built from the **completion** `Â = (Â, (A⁺)^{c+})`. We therefore want, throughout, to "assume `A` complete" — this is licensed by **Proposition 7.48** (§2.2/§8.1) and is the crux of the chapter.

### 2.2. References

The textbook we follow:

> **[W]** Torsten Wedhorn. *Adic Spaces*. Lecture notes, arXiv:1910.05934 (2019). All theorem/lemma/example numbers in this brief are Wedhorn's, from this version (pp. 49–105).

Huber's papers, cited by Wedhorn's bibliography keys:

> **[Hu2]** R. Huber. *Continuous valuations*. Math. Z. **212** (1993), 445–477. — Wedhorn's Proposition 7.48 is proved by citing **[Hu2] Prop. 3.9**.
>
> **[Hu3]** R. Huber. *A generalization of formal schemes and rigid analytic varieties*. Math. Z. **217** (1994), 513–551. — Source of Wedhorn's Lemma 2.4 (= Wedhorn 6.16/6.18) and Lemma 2.6 (= Wedhorn 7.54).

*A small bibliographic uncertainty we'd like settled (see Q6):* an internal note once recorded `[Hu2]` as Huber's 1990 Habilitationsschrift *Bewertungsspektrum und rigide Geometrie* rather than *Continuous valuations*. We have used the expansion read directly from Wedhorn's bibliography (*Continuous valuations*, Math. Z. 212, Prop. 3.9). If the reviewer knows where the statement "`Spa Â → Spa A` is a homeomorphism preserving rational subsets" actually lives, that pin-down would help.

Supporting analysis references actually used in the proofs:

> **[BGR]** S. Bosch, U. Güntzer, R. Remmert. *Non-Archimedean Analysis*. Grundlehren 261, Springer (1984). Used: §3.7.2/1–2 and §3.7.3/2–3 + Cor. 5 (closed-submodule and unique-module-topology theory).
>
> **[He]** Timo Henkel. *An open mapping theorem for rings which have a zero sequence of units*. arXiv:1407.5647 (2014). Supplies the open mapping theorem for Tate-type modules with **no σ-compactness or local-compactness hypothesis** (Wedhorn was the advisor). Used to fill Wedhorn 6.16.
>
> **[Bbk]** N. Bourbaki. *Topologie Générale*, Ch. III §3 no. 3, Théorème 1 (the group-level open-mapping theorem underlying [He]).

The augmented-Čech machinery is Wedhorn's **Appendix A** (Definition A.1, Remark A.2, Proposition A.3, Proposition A.4), with the cohomology-comparison step citing Cartan via Godement.

### 2.3. State of the art

Theorem 8.28 is classical (Huber's foundational work; Wedhorn's notes are exposition). The interest here is the **formalisation**: to our knowledge there is no prior machine-checked proof of acyclicity of rational coverings for adic spectra of strongly-noetherian Tate rings. Notably, three of Wedhorn's inputs — **Theorem 6.16, Proposition 6.17, Proposition 6.18** — are stated in [W] with the literal text **"Proof. Missing"** (deferred to [Hu3]/[BGR]). We have now supplied machine-checked proofs of all three (§5), so the formalisation is in places more complete than the source notes.

---

## 3. Strategy

Wedhorn's proof of 8.28(b) is the following chain, which we mirror leaf-for-leaf.

1. **Proposition A.4** reduces "`𝒪_X` is a sheaf and `Hq = 0` for `q ≥ 1`" to: *every covering of a rational subset by rational subsets is `𝒪_X`-acyclic* (the augmented alternating Čech complex `0 → 𝒪_X(U) → Č⁰ → Č¹ → …` is exact). The leading `0 → 𝒪_X(U) →` term is the injectivity/separatedness of the augmentation.
2. We may assume `A` **complete** (Proposition 7.48: `Spa Â → Spa A` is a homeomorphism carrying rational subsets to rational subsets, so the situation is unchanged on passing to `Â`).
3. **Lemma 7.54** refines any covering to a *rational cover generated by* a finite `T ⊆ A` with `T·A = A`. By **Proposition A.3(2)** (refinement-invariance of acyclicity), it suffices to prove acyclicity for these.
4. **Lemma 8.34** proves acyclicity of `T`-generated covers by a four-step induction: (i) single-element **Laurent covers** `{x(f) ≤ 1} ∪ {x(f) ≥ 1}` are acyclic by **Lemma 8.33**, and products of Laurent covers are acyclic by **Proposition A.3(3)**; (ii) **Corollary 7.32** produces a unit dominating the `fᵢ`, reducing a general `T`-cover (after restricting to a suitable Laurent cover) to one generated by *units*; (iii) unit-generated covers are refined by Laurent covers; (iv) **Proposition A.3(1)** transfers acyclicity from the Laurent cover to the original.
5. **Lemma 8.33** (the two-set Laurent base case) is a 3×3 diagram chase whose top input is that the augmentation `ε` is **injective** — which is **Corollary 8.32**.
6. **Corollary 8.32**: for a finite rational cover, `𝒪_X(X) → ∏ᵢ 𝒪_X(Uᵢ)` is **faithfully flat** (in particular injective). This is "immediate" from:
   - **Proposition 8.30**: each restriction `𝒪_X(V) → 𝒪_X(U)` (for `U ⊆ V` rational) is **flat**; plus
   - the covering condition ⟹ the product is *faithfully* flat (every maximal ideal of `𝒪_X(X)` survives in some factor).
7. **Proposition 8.30** is proved by: **Example 6.38** (`𝒪_X(V)` is again strongly noetherian, and `𝒪_X(U₁) = Â⟨X⟩/(f−X)`, `𝒪_X(U₂) = Â⟨X⟩/(1−fX)` for the two basic Laurent shapes), **Remark 7.55** (any `U ⊆ V` is reached by a finite chain of basic Laurent steps), and **Lemma 8.31** (those two quotients are flat over `A`).
8. **Lemma 8.31** ⟸ **Remark 8.29** (the isomorphism `M ⊗_A A⟨X⟩ ≅ M⟨X⟩` for finitely generated `M`), which uses **Proposition 6.18** (canonical module topology + continuity/openness) and **Proposition 6.17** (closed-ideal ⟺ noetherian).

Finally, the **topological-embedding** half of "sheaf of *topological* rings" (Remark 8.20(b)) is obtained from the acyclicity — which exhibits `𝒪_X(U) → ∏ᵢ 𝒪_X(Uᵢ)` as a continuous injection onto `ker δ⁰`, a *complete* equaliser — together with the **Banach open mapping theorem** (Wedhorn 6.16): a continuous bijection of complete Tate-type modules is open, so the embedding is topological.

**The two genuinely-external dependencies of this strategy:**

- **(D1)** Proposition 7.48 (`Spa Â ≅ Spa A`), which Wedhorn proves only by citing [Hu2] 3.9, feeding the injective/faithfully-flat half (step 6).
- **(D2)** the Appendix-A Čech machinery (Prop A.3/A.4) plus Lemmas 8.33/8.34 — substantial but standard homological/combinatorial work — feeding *both* the gluing and (via the equaliser + the open mapping theorem) the topological inducing.

Everything else in the chain we have formalised sorry-free (§5).

---

## 4. Definitions (the formalisation-specific objects)

The adic-spaces notions (affinoid ring, `Spv`, `Spa`, rational subset, continuous valuation) are Wedhorn's and we will not restate them. The objects worth pinning down:

**Definition 4.1 (the presheaf value).** For a rational subset `U = R(T/s)`, the value `𝒪_X(U)` is the completion of the localisation `A[T/s]` for the natural ring topology making `T/s` power-bounded. It is a complete Tate ring. Restriction `𝒪_X(V) → 𝒪_X(U)` for `U ⊆ V` is the induced continuous homomorphism.

**Definition 4.2 (sheafy, as formalised).** `𝒪_X` is **sheafy** iff for every finite rational covering `C = (Uᵢ)` of every rational `U`:
- *(embedding)* the product-of-restrictions `𝒪_X(U) → ∏ᵢ 𝒪_X(Uᵢ)` is a topological embedding; and
- *(gluing)* for every family `(gᵢ)` with `gᵢ ∈ 𝒪_X(Uᵢ)` agreeing on every overlap (stated via arbitrary rational `D₃` contained in both `Uᵢ, Uⱼ`), there exists `x ∈ 𝒪_X(U)` with `x|_{Uᵢ} = gᵢ` for all `i`.

This is exactly Remark 8.20's criterion: *(gluing)* + the injective part of *(embedding)* is the sheaf-of-rings axiom; the inducing part of *(embedding)* is the topological refinement upgrading "sheaf of rings" to "sheaf of *topological* rings".

**Definition 4.3 (strongly noetherian, as formalised).** `A` is *strongly noetherian* iff the restricted power-series subring in `k` variables is noetherian for every `k ∈ ℕ`. (Wedhorn 6.36(i); `k=0` recovers `A` noetherian when `A` complete.)

**Definition 4.4 (the standing hypotheses on `A`).** The headline theorem is stated under: `A` a complete f-adic/Tate ring, Hausdorff, with `A⁺` the plus-bounded subring; `A` **noetherian** and **strongly noetherian**; and `A` **nonarchimedean** in the sense of a neighbourhood basis of `0` by subgroups (Wedhorn 5.23/5.30, an instance for Huber rings). We deliberately do **not** assume `A` a domain, that any ring of definition `A₀` is noetherian, or that `Aⁿ` is σ-compact — see §8.4.

---

## 5. Established results (formalised, machine-checked, sorry-free)

Ordered foundations-first. Each is fully proved; several are verified axiom-clean (depend only on Mathlib's classical foundations, no `sorry`, no added axioms).

**Theorem 5.1 (Banach open mapping for Tate modules; Wedhorn 6.16, "Proof. Missing" in [W]).** *Let `A` be a topological ring possessing a sequence of units converging to `0` (e.g. any Tate ring). Let `M, N` be Hausdorff topological `A`-modules each with a countable neighbourhood basis at `0`, with `M` complete. A continuous `A`-linear surjection `M → N` with `N` complete is open.*

*Sketch.* We follow [He]/[Bbk], not the classical σ-compact Banach argument (σ-compactness fails for `Aⁿ` over a Tate ring — §8.4). The argument has the usual two-step shape. **Step 1 (almost-open):** fix a neighbourhood `V` of `0` in `M`; we show `closure(f(V))` is a neighbourhood of `0` in `N`. Here the classical proof covers `N` by countably many translates of a *compact* set and invokes Baire; that compactness is unavailable. Instead we use the **dilation cover**: writing `ϖₙ → 0` for a sequence of *units* of `A` converging to `0`, the sets `ϖₙ⁻¹·V` exhaust `M`, so `N = ⋃ₙ f(ϖₙ⁻¹·V) = ⋃ₙ ϖₙ⁻¹·f(V)`; since `N` is a complete (hence Baire) first-countable group and each `ϖₙ⁻¹·f(V)` is a translate-stable dilate, some `closure(ϖₙ⁻¹·f(V))` — equivalently `closure(f(V))` after rescaling by the unit `ϖₙ` — has nonempty interior, and a difference argument centres it at `0`. **Step 2 (open):** the standard completeness iteration: given almost-openness at every scale, a Cauchy series construction (using completeness of `M` and first-countability) upgrades `0 ∈ int(closure(f(V)))` to `0 ∈ int(f(V'))` for a slightly larger `V'`, so `f` is open. The "any two of {`N` complete, `f` surjective, `f` open} imply the third" form follows by symmetry; we only need "complete + surjective ⟹ open". ∎

> **Remark.** The countability hypothesis is *first-countability* (countable neighbourhood basis), **not** σ-compactness — essential, since the Tate modules that occur (e.g. `Â⟨X⟩`, `Aⁿ`, `𝒪_X(V)`) are first-countable but not σ-compact. The role classically played by local compactness/σ-compactness is played here by the *zero-sequence of units* `ϖₙ → 0`, which is exactly what a Tate ring provides and what [He] is built around.

**Theorem 5.2 (closed-submodule criterion; [BGR] §3.7.2/1).** *Over a complete first-countable Tate ring `A`, a submodule `N` of a complete first-countable Tate `A`-module `M` whose topological closure is module-finite is closed.* With Theorem 5.1 this yields **Wedhorn 6.17** (complete Tate ring noetherian ⟺ every ideal closed) and **Wedhorn 6.18** (every f.g. module over a complete noetherian Tate ring has a unique complete first-countable module topology; `A`-linear maps of such are continuous and open onto image) — both also "Proof. Missing" in [W].

**Theorem 5.3 (Remark 8.29; the `μ_M` isomorphism).** *For `A` complete noetherian Tate and `M` finitely generated with its canonical topology (Theorem 5.2/6.18(1)), the natural `A⟨X⟩`-linear map `μ_M : M ⊗_A A⟨X⟩ → M⟨X⟩`, `m ⊗ a ↦ m·a`, is bijective.* Here `M⟨X⟩` denotes the module of restricted power series `Σ_{ν≥0} mν Xν` with `mν ∈ M` such that, for every neighbourhood `U` of `0` in `M`, `mν ∈ U` for almost all `ν`.

*Sketch.* For finite free `M = Aᵐ` the claim is clear (`μ` is the identification `(A⟨X⟩)ᵐ ≅ (Aᵐ)⟨X⟩`). For general `M`, noetherianity gives a finite presentation `Aⁿ → Aᵐ → M → 0`. By Theorem 6.18(2) the maps are continuous and open onto their images, so applying the (right-exact) functors "`− ⊗_A A⟨X⟩`" and "`(−)⟨X⟩`" yields a commuting ladder with exact rows
`Aⁿ⟨X⟩ → Aᵐ⟨X⟩ → M⟨X⟩ → 0` and `Aⁿ⊗A⟨X⟩ → Aᵐ⊗A⟨X⟩ → M⊗A⟨X⟩ → 0`,
in which the two left vertical maps `μ_{Aⁿ}, μ_{Aᵐ}` are the free-case isomorphisms. The five-lemma then forces `μ_M` to be an isomorphism. The openness in 6.18(2) is what makes the top row exact at `M⟨X⟩` (the restricted-power-series condition is preserved), and is precisely where the analysis (Theorem 5.1/5.2) enters. ∎

**Theorem 5.4 (Lemma 8.31; flatness of the basic Laurent quotients).** *For `A` complete noetherian Tate and `f ∈ A`: `A⟨X⟩` is faithfully flat over `A`, and both `A⟨X⟩/(f−X)` and `A⟨X⟩/(1−fX)` are flat over `A`.*

*Sketch.* **Flatness of `A⟨X⟩`:** for an injection `i : N ↪ M` of f.g. modules, Theorem 5.3 identifies `i ⊗ id_{A⟨X⟩}` with the coefficient-wise map `N⟨X⟩ → M⟨X⟩`, which is injective; so `A⟨X⟩` is flat. **Faithful** flatness: for a prime `p ⊂ A`, the set of `Σ aν Xν ∈ A⟨X⟩` with `a₀ ∈ p` is a prime `q` with `q ∩ A = p`, so `Spec A⟨X⟩ → Spec A` is surjective.
**The two quotients.** Writing `B = A⟨X⟩/(g)`, reduce its flatness to a single claim: *for every f.g. `M`, multiplication-by-`g` on `M⟨X⟩` is injective.* Indeed `0 → A⟨X⟩ →·g A⟨X⟩ → B → 0` is exact (claim at `M = A`); to get `Tor₁ᴬ(M, B) = 0` it suffices (flatness of `A⟨X⟩` + long exact `Tor`) that `id_M ⊗ (·g)` be injective, and by Theorem 5.3 that map *is* multiplication-by-`g` on `M⟨X⟩`. Now: for `g = 1 − fX`, multiplication-by-`g` on `M⟨X⟩` is visibly injective (compare top-degree coefficients). For `g = f − X`, a putative kernel element `u = Σ mν Xν` satisfies the recurrence `f·m₀ = 0` and `f·mν = m_{ν−1}` (all `ν ≥ 1`); the submodule `M′ = ⟨mν⟩` is f.g. (noetherian), say by `m₀,…,m_l`, whence the recurrence gives `M′ = A·m_l` with `f^{l+1}·m_l = 0`; writing `m_{2l+1} = a·m_l` yields `m_l = f^{l+1} m_{2l+1} = a f^{l+1} m_l = 0`, so `M′ = 0` and `u = 0`. ∎

**Theorem 5.5 (Corollary 7.32).** *For a Tate affinoid `A`, quasi-compact `Y ⊆ Spa A`, and `s ∈ A` with `|s(y)| ≠ 0` on `Y`, there is a unit `π ∈ A×` with `|π(y)| < |s(y)|` on `Y`.* (The dominating-unit input to Lemma 8.34(ii); sorry-free.)

**Theorem 5.6 (base-change strong-noetherianity; Example 6.38).** *If `A` is strongly noetherian Tate and `U = R(T/s)` rational, then `𝒪_X(U) = Â⟨T/s⟩` is again strongly noetherian.*

*Sketch (Wedhorn's actual argument, which we follow exactly — an earlier attempt to invent a "ring-of-definition surjectivity" route was a misread and was discarded).* The map `ι : A → Â⟨T/s⟩` is adic by construction, and `A[M]` (with `M = {t/sᵢ}`) is dense in `Â⟨T/s⟩` while `A₀[M]` is dense in `Â₀⟨T/s⟩`, so `ι` is **topologically of finite type**. To see `Â⟨T/s⟩` is noetherian, present it as `C/a`: set `C = Â⟨X_{i,t}⟩` (the completed/restricted power-series ring in the variables `X_{i,t}`) and `a = (t − sᵢ X_{i,t})_{i,t}`. Then `C` is noetherian (strong-noetherianity of `A`), so `a` is a **closed** ideal by **Proposition 6.17**; since `A` is Tate, `Tᵢ·A = A` (Remark 7.30(2)), so the image of each `sᵢ` in `C/a` is a unit; and one checks `A → Â⟨T/s⟩` and `A → C/a` satisfy the *same universal property* (sending `X_{i,t} ↦ t/sᵢ`), giving `Â⟨T/s⟩ ≅ C/a`, a noetherian quotient of `C`. Finally **Remark 6.37(1)** (t.f.t. over strongly-noetherian Tate ⟹ strongly noetherian) upgrades "noetherian" to "strongly noetherian". To make this run in the formaliser we built the **general `n`-variable restricted-power-series Tate topology** for `C` (Wedhorn Prop 6.21(2): ring of definition `Â₀⟨X⟩`, ideal of definition `I·Â₀⟨X⟩`), proved it a complete Tate topology, and proved Proposition 6.17 ("every ideal of `C` is closed") for it via Theorem 5.2 — all sorry-free. The closed-image/comparison isomorphism `C/ker ≅ 𝒪_X(U)` then transports noetherianity. ∎

**Theorem 5.7 (per-step flatness for Proposition 8.30; the basic Laurent step).** *The restriction to a basic Laurent sub-locale `𝒪_X(V) → 𝒪_X(V₁)` (and the `≥`-side) is flat,* via the relative form of Example 6.38 over the base `𝒪_X(V)` and Theorem 5.4 transported across the explicit presentation isomorphism. Sorry-free, with no noetherian-ring-of-definition or domain hypotheses.

**Theorem 5.8 (faithful flatness from a maximal-ideal criterion).** *A finite product of flat `R`-algebras `Bᵢ` such that every maximal ideal `m ⊂ R` has `m·Bᵢ ≠ Bᵢ` for some `i` is faithfully flat over `R`.* (A clean Mathlib-level lemma; the abstract engine for Corollary 8.32, once Proposition 8.30 supplies flatness and Proposition 7.48 supplies the maximal-ideal/cover bridge.)

**Theorem 5.9 (complete-affinoid Nullstellensatz inputs; Wedhorn 7.45/7.52(2)).** *For a complete affinoid `A` (with `A⁺ ⊆ A₀`): every maximal ideal `m` is `≤ supp v` for some `v ∈ Spa A`; equivalently `f ∈ A` is a unit iff no `v ∈ Spa A` has `v(f) = 0`.* Sorry-free; gives support/maximal-ideal control on the completion (without a noetherian ring of definition).

**Theorem 5.10 (the "extension to the cover" direction of the Spa correspondence).** *For a rational `U` and a continuous valuation `v` on `A` lying in `U`, there is `w ∈ Spa 𝒪_X(U)` restricting to `v` along the canonical map.* Sorry-free; this is the "⊇" half of the local Spa–completion comparison. The missing half is the injectivity, §8.1.

---

## 6. In progress (statements fixed; proofs assembled but resting on the open leaves of §8)

**6.1 The headline assembly (sheafy theorem).** Stated as `(embedding) ∧ (gluing)` (Definition 4.2) under the standing hypotheses (Definition 4.4). The assembly is in place; its two fields reduce to:
- *(embedding)* = *(injective)* + *(inducing)*. The **injective** half is fully reduced to Corollary 8.32 (faithfully flat ⟹ injective), complete *given* §8.1. The **inducing** half is reduced to the acyclicity equaliser + Theorem 5.1, complete *given* §8.2.
- *(gluing)* = Lemma 8.34 (acyclicity); complete *given* §8.2.

**6.2 Proposition 8.30 (each restriction flat).** Reduction in place: Example 6.38 (Theorem 5.6) to reduce to `X = V` complete, Remark 7.55 to a chain of basic Laurent steps, Theorem 5.7 per step composed by transitivity of flatness. The one open node is the **Remark 7.55 chain construction** (assembling the nested rational subsets `V = X₀ ⊇ … ⊇ Xₙ = U`) — geometric bookkeeping, no new deep input.

**6.3 Corollary 8.32 (faithfully flat, injective).** Reduced to Proposition 8.30 (flat factors) + Theorem 5.8 (abstract faithful flatness) + the **maximal-ideal/cover bridge** "every maximal of `𝒪_X(X)` has `m·𝒪_X(Uᵢ) ≠ 𝒪_X(Uᵢ)` for some `i`". That bridge reduces to Proposition 7.48 (§8.1). The abstract criterion and flat inputs are done; only the bridge is open.

**6.4 A faithful re-derivation of strong-noetherianity for presheaf values** (Remark 6.37(1)). Needed so the chain "`A` strongly noetherian ⟹ `𝒪_X(U)` strongly noetherian" is supplied by the *correct* t.f.t. argument, not the false "noetherian ⟹ strongly noetherian" shortcut (§8.3). Statement fixed; proof in progress.

---

## 7. Targets and the ticket board

Work is tracked on a board; the mathematically-meaningful current tickets, in dependency order (✅ done / 🔧 reduced-but-open / 🔴 deep-open / ⏸ deferred):

| Ticket (meaning) | Mathematical statement | Status | Depends on |
|---|---|---|---|
| `base-change-noetherian` (Example 6.38) | `𝒪_X(U)` strongly noetherian; general `n`-variable Tate topology + 6.17 for it | ✅ | 5.2 |
| `lemma-8-31-laurent-flat` | the two basic Laurent quotients are flat | ✅ | 5.3 |
| `prop-8-30-per-step` | one basic Laurent restriction is flat | ✅ | 5.4, 5.6 |
| `faithfully-flat-via-maximals` | product of flats + maximal criterion ⟹ faithfully flat | ✅ | — |
| `nullstellensatz-7-52` | unit ⟺ nowhere-zero on `Spa`; maximal `≤ supp` | ✅ | — |
| `spa-extension-⊇` | extend a valuation from `A` to `𝒪_X(U)` | ✅ | — |
| `prop-8-30-remark755-chain` | assemble the Remark 7.55 nested-locale chain | 🔧 | per-step |
| `cor-8-32-maximal-bridge` | every maximal of `𝒪_X(X)` survives in some `𝒪_X(Uᵢ)` | 🔧 | `spa-extension-along-restriction` |
| `presheafValue-strongly-noeth` | `𝒪_X(U)` strongly noetherian via t.f.t. (Remark 6.37(1)) | 🔧 | base-change |
| **`spa-extension-along-restriction`** | lift Spa points along a restriction; rests on `Spa Â ≅ Spa A` | 🔴 | **[Hu2] 3.9** |
| **`completion-spa-injective`** | `comap` of the completion map is injective on `Spa` | 🔴 | **[Hu2] 3.9** |
| `topological-inducing` | `𝒪_X(U) → ∏ 𝒪_X(Uᵢ)` is inducing | 🔴→🔧 | acyclicity + 5.1 |
| `lemma-8-33-laurent-gluing` | two-set Laurent augmented complex exact | ⏸ | Cor 8.32, Prop A.3 |
| `lemma-8-34-gluing` | `T`-generated covers acyclic (the (i)–(iv) induction) | ⏸ | 8.33, A.3, 7.32 |
| Appendix-A Čech machinery | Definition A.1, Prop A.3(1)(2)(3), Prop A.4 | ⏸ | — |

The ⏸ Čech block (Lemma 8.33/8.34 + Appendix A) is a self-contained sub-project of roughly two dozen open leaves — "substantial but standard" — not yet decomposed in detail.

---

## 8. Where we're stuck

### 8.1 The one genuinely-deep external dependency: Proposition 7.48 = [Hu2] 3.9

> **Proposition 7.48 [W].** *For an affinoid ring `A`, the canonical map `Spa Â → Spa A` is a homeomorphism which maps rational subsets to rational subsets.* Wedhorn's entire proof is the citation **"[Hu2] Prop. 3.9"**.

In the formalisation this surfaces as two open leaves, both forms of "the completion map induces an injection on adic spectra":
- *injectivity*: two continuous valuations on `𝒪_X(U)` (a completed localisation) with equal pullback to the localisation are equal; and
- *the lifting/extension along a restriction* used in the maximal-ideal bridge of Corollary 8.32 (§6.3): a Spa point of `𝒪_X(X)` whose shadow lies in `Uᵢ` lifts to a Spa point of `𝒪_X(Uᵢ)`.

We have the **surjective/extension ("⊇")** direction sorry-free (Theorem 5.10). The **injectivity** is the gap. It is exactly the content Wedhorn defers to Huber, and it is the only place in the whole 8.28(b) chain where we hit something Wedhorn himself does not prove.

**Why it is needed.** Corollary 8.32's "faithfully flat" requires the covering `(Uᵢ)` to be *jointly conservative on maximal ideals* of the completed global ring `𝒪_X(X)`: every maximal `m` must survive in some `𝒪_X(Uᵢ)`. Translating the geometric covering `⋃ Uᵢ = X` into this algebraic statement *about the completion* is precisely the Spa–completion correspondence (Prop 7.48): a maximal surviving nowhere would give a point of `Spa 𝒪_X(X) ≅ Spa A` outside every `Uᵢ`. We see no way to get faithful flatness without this bridge.

**What we've ruled out.** We previously routed Corollary 8.32 through a *prime-surjection* criterion (lifting primes through each restriction); that required a Bourbaki rank-1 domination statement we could not supply, and we deleted it. The current maximal-ideal route (Theorem 5.8) is clean *modulo* 7.48 and we believe it the faithful one. The "⊇" direction is genuinely the easy half and is done.

This is the subject of Q1–Q3.

### 8.2 The Čech-acyclicity layer (Lemmas 8.33/8.34 + Appendix A) — substantial but standard

This block feeds *both* the gluing field and (via the equaliser exactness + the landed open mapping theorem, Theorem 5.1) the topological-inducing field. We regard it as standard homological algebra + the combinatorics of Laurent refinements, and its one genuinely-analytic input (the open mapping theorem) is **already done** (Theorem 5.1, no σ-compactness). We have not yet carried it out in detail. **The full statements the reviewer can audit are reproduced in Appendix A (§10)**: Definition A.1 (acyclic cover), Proposition A.3(1)(2)(3) (the acyclicity-transfer toolkit), Proposition A.4 (acyclicity ⟹ sheaf + `Hq = 0`), the explicit Laurent presentations (8.2.1), the 3×3 diagram and chase of Lemma 8.33, and the four-step induction of Lemma 8.34.

The specific leaves we'd most like sanity-checked:
- **the 3×3 diagram chase of Lemma 8.33** — three rows with exact columns (the columns being exact by the presentations 8.2.1), where the bottom row's exactness is deduced from the exactness of the top two rows together with the injectivity of `ε` (= Corollary 8.32, hence §8.1). We want to confirm there is no hidden analytic subtlety in running this chase over *completed* rings `A⟨ζ⟩`, `A⟨η⟩`, `A⟨ζ,ζ⁻¹⟩` rather than classical affinoid Banach algebras, and that the surjectivity of `λ, λ′` really does follow from the displayed decompositions `A⟨ζ,ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹A⟨ζ⁻¹⟩` and `(f−ζ)A⟨ζ,ζ⁻¹⟩ = (f−ζ)A⟨ζ⟩ + (1−fζ⁻¹)A⟨ζ⁻¹⟩`;
- **the refinement transfer Proposition A.3(1)/(2)/(3)** — purely formal once the hypotheses are arranged, but we'd like confirmation that the "`Ȟq(U,F) = Ȟq(V,F)` for all `q`" claim underlying A.3(1) holds at this generality (presheaf of complete topological *abelian groups*, forgetting the ring/topology), so that A.3 is genuinely a statement about presheaves of abelian groups (which is how Wedhorn states Appendix A);
- **the Cartan/Godement comparison** in Proposition A.4 (`Ȟq ≅ Hq`), which we intend to cite rather than reprove.

### 8.3 Two statements we found to be FALSE-as-stated, and the faithful repairs

Two tempting shortcuts are false in the generality we need (both fail for `A = ℂ_p`); we'd appreciate a sanity-check of the repairs:

- **"noetherian Tate ⟹ strongly noetherian."** False (a noetherian Tate ring need not have `A⟨X⟩` noetherian). It had crept in as a converter. **Repair:** Remark 6.37(1) — `𝒪_X(U)` is *topologically of finite type* over the strongly-noetherian `A`, hence strongly noetherian, never going through "noetherian" as an intermediate.
- **"strongly noetherian Tate ⟹ some ring of definition is noetherian."** False (`ℂ_p` is strongly noetherian Tate with no noetherian ring of definition). Several earlier proofs assumed a noetherian ring of definition `A₀`; we have migrated every critical-path signature to *ring-level* noetherianity/strong-noetherianity of `A` itself, never `A₀`. (The single most pervasive defect we corrected.)

### 8.4 Hypotheses we deliberately avoid (and why)

To reassure the reviewer we are not smuggling strength:
- **No `IsDomain A`** — 8.28(b) is about general strongly-noetherian Tate rings.
- **No noetherian ring of definition** — false for `ℂ_p` (§8.3).
- **No σ-compactness of `Aⁿ`** — false for Tate rings (e.g. `ℂ((t))`); hence the [He] open mapping theorem rather than the classical σ-compact Banach argument.
- **No "open-ideal neighbourhood basis" (linear topology)** — unsatisfiable for any nontrivial Tate ring (a topologically nilpotent unit forces every open ideal to be the whole ring). We use the nonarchimedean-subgroup-basis notion (Wedhorn 5.23/5.30).

We apply a standing "`ℂ_p` test" to every hypothesis: if it fails for `ℂ_p` (which satisfies 8.28(b)), it is unfaithful and rejected.

---

## 9. Open mathematical questions for the reviewer

**Q1 (headline strategic question).** Is the route to Corollary 8.32's *faithful* flatness via "Proposition 8.30 (flat factors) + the maximal-ideal/cover bridge, with the bridge supplied by Proposition 7.48" the right one — and, more sharply, **is the full homeomorphism `Spa Â ≅ Spa A` (preserving rational subsets) genuinely needed**, or does Corollary 8.32 only require a *weaker* consequence (e.g. surjectivity onto the cover's points, or just injectivity of the support map on maximal ideals)? If a weaker statement suffices, identifying it would let us avoid formalising all of [Hu2] 3.9.

**Q2.** What is the **cleanest machine-formalisable proof of `Spa Â ≅ Spa A`** (Prop 7.48 / [Hu2] 3.9)? In particular, can the injectivity half (two continuous valuations on the completion agreeing on the dense subring are equal) be proved *directly* from continuity + density + the valuation-spectrum topology, without reproducing the apparatus of [Hu2] §3? We have the surjective/extension direction already; is the injective direction comparably elementary, or does it genuinely need Huber's machinery?

**Q3.** Is there an **alternative route to Corollary 8.32 (or to the whole acyclicity) that never invokes the Spa–completion correspondence** — e.g. a purely algebraic argument that the span condition `T·A = A` directly forces faithful flatness of `∏ 𝒪_X(Uᵢ)` over `𝒪_X(X)` after completion (via the explicit Laurent presentations of Examples 6.38/6.39 and a Čech-style algebraic computation), bypassing maximal ideals entirely? Wedhorn calls 8.32 "immediate" from 8.30 + the covering; what does he intend by "immediate", and does it hide a use of 7.48 or sidestep it?

**Q4 (soundness of the packaging).** Is our packaging of "sheaf of complete topological rings" as *(embedding = topological embedding) ∧ (gluing = amalgamation)* — i.e. Remark 8.20's criterion — the right target, and is it legitimate to obtain the topological-embedding (inducing) part *a posteriori* from acyclicity + the open mapping theorem (Theorem 5.1), rather than directly? We want to be sure this is not circular and that the open-mapping route to inducing is faithful.

**Q5 (the analysis inputs).** We supplied machine-checked proofs of Wedhorn 6.16/6.17/6.18 (which [W] marks "Proof. Missing") via [He] (zero-sequence-of-units open mapping, no σ-compactness) and [BGR] §3.7.2–3. Are these the proofs the reviewer would expect, and is the [He] route (rather than a classical Banach/σ-compact route) the correct way to handle the open mapping theorem for the modules that occur over a general Tate ring?

**Q6 (bibliographic).** Which Huber source actually contains "`Spa Â → Spa A` is a homeomorphism preserving rational subsets" as Prop. 3.9 — *Continuous valuations* (Math. Z. 212, 1993) or the 1990 Habilitationsschrift? (See §2.2.) The exact location helps us target the formalisation of D1.

---

## 10. Appendix A — the Čech-acyclicity layer in full (dependency D2)

Reproduced here, faithful to Wedhorn, so the reviewer can audit the layer that feeds both the gluing field and (with Theorem 5.1) the topological inducing. Throughout, `F` is a presheaf of *abelian groups* on `X`; for an open cover `U = (Uᵢ)ᵢ` the alternating Čech groups `Čq(U,F)` and differentials `dq` are the usual ones, and `ε : F(X) → Č⁰(U,F)`, `s ↦ (s|U)`, is the augmentation.

**Definition A.1 (`F`-acyclic cover).** `U` is *`F`-acyclic* if the augmented complex `0 → F(X) → Č⁰(U,F) → Č¹(U,F) → Č²(U,F) → …` is exact; equivalently `ε` induces `F(X) ≅ Ȟ⁰(U,F)` and `Ȟq(U,F) = 0` for `q ≥ 1`. The leading `0 → F(X) → Č⁰` exactness is exactly injectivity of `ε` together with `im ε = ker d⁰` (the sheaf axiom for `U`).

**Remark A.2.** Acyclicity is invariant under mutual refinement; any cover one of whose members is `X` itself is `F`-acyclic.

**Proposition A.3 (acyclicity transfer).** Let `U = (Uᵢ)ᵢ`, `V = (Vⱼ)ⱼ` be open covers of `X` with `V|_{U_{i₀…iq}}` `F`-acyclic (more precisely `F|_{U_{i₀…iq}}`-acyclic) for all index tuples and all `q ≥ 0`. Then:
1. if moreover `U|_{V_{j₀…jq}}` is `F`-acyclic for all tuples and all `q`, then `U` is `F`-acyclic ⟺ `V` is `F`-acyclic (indeed `Ȟq(U,F) = Ȟq(V,F)` for all `q`);
2. if `V` refines `U`, then `U` is `F`-acyclic ⟺ `V` is `F`-acyclic;
3. `U × V` is `F`-acyclic ⟺ `U` is `F`-acyclic.

**Proposition A.4 (acyclicity ⟹ sheaf + vanishing).** Let `B` be a basis of `X` stable under finite intersection (for `X = Spa A`, the rational subsets, by Remark 7.30(5)). Let `F′` be a presheaf of abelian groups on `B`, and `F(V) = lim_{U ⊆ V, U ∈ B} F′(U)`. If for every `U ∈ B` and every cover of `U` by members of `B` the presheaf `F` is acyclic, then `F` is a **sheaf** on `X`, and for every open `U ⊆ X` and all `q ≥ 0` the canonical map `Ȟq(U,F) → Hq(U,F)` is an isomorphism; in particular `Hq(U,F) = 0` for `U ∈ B`, `q ≥ 1`. (The sheaf conclusion comes from the leading `0 → F(U) → Č⁰ → Č¹` exactness; the comparison `Ȟq ≅ Hq` is Cartan's theorem, cited via Godement.)

This is the entry point of the whole proof: Theorem 8.28(b) is "apply A.4 with `F = 𝒪_X` and `B =` rational subsets", and the hypothesis "every basis-cover is acyclic" is supplied by Lemma 8.34 below (after the Lemma 7.54 refinement and A.3(2)).

### Lemma 8.33 (the two-set Laurent base case)

> **Lemma 8.33.** *Let `A` be a strongly noetherian Tate affinoid, `X = Spa A`, `f ∈ A`, `U₁ = {x : x(f) ≤ 1}`, `U₂ = {x : x(f) ≥ 1}`. Then the augmented alternating Čech complex for `{U₁, U₂}`,*
> `0 → 𝒪_X(X) →ε 𝒪_X(U₁) × 𝒪_X(U₂) →δ 𝒪_X(U₁ ∩ U₂) → 0`, *is exact.*

**Explicit presentations (Wedhorn's (8.2.1), from Examples 6.38/6.39),** assuming `A` complete (allowed by 7.48):
```
𝒪_X(U₁)      = A⟨ζ⟩/(f − ζ)
𝒪_X(U₂)      = A⟨η⟩/(1 − fη)
𝒪_X(U₁∩U₂)  = A⟨ζ,η⟩/(f − ζ, 1 − fη)  =  A⟨ζ,η⟩/(f − ζ, 1 − ζη)  =  A⟨ζ, ζ⁻¹⟩/(f − ζ)
```

**The 3×3 diagram** (all columns exact by the presentations above):
```
0 →  A  →   (f−ζ)A⟨ζ⟩ × (1−fη)A⟨η⟩   →λ′   (f−ζ)A⟨ζ,ζ⁻¹⟩      → 0
        │              │                              │
0 →  A  →ι       A⟨ζ⟩ × A⟨η⟩          →λ      A⟨ζ,ζ⁻¹⟩          → 0
        │              │                              │
0 →  A  →ε   𝒪_X(U₁) × 𝒪_X(U₂)       →δ    𝒪_X(U₁∩U₂)        → 0
```
Here `ι` is the canonical (diagonal) injection, `λ(g(ζ), h(η)) = g(ζ) − h(ζ⁻¹)`, and `λ′` is the map `λ` induces on the top row.

**The chase.** The columns are exact by (8.2.1). A diagram chase shows that if the top two rows are exact then the bottom row is exact — *using that we already know `ε` is injective* (Corollary 8.32, hence §8.1). Exactness of the top two rows reduces to:
- **surjectivity of `λ` and `λ′`**, from the decompositions `A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹A⟨ζ⁻¹⟩` and `(f−ζ)A⟨ζ, ζ⁻¹⟩ = (f−ζ)A⟨ζ⟩ + (1 − fζ⁻¹)A⟨ζ⁻¹⟩`; and
- **`im ι = ker λ`**, from the coefficient computation: `0 = λ(Σ aₖ ζᵏ, Σ bₖ ηᵏ) = Σ aₖ ζᵏ − Σ bₖ ζ⁻ᵏ` forces `aₖ = bₖ = 0` for `k > 0` and `a₀ = b₀`.

### Lemma 8.34 (general `T`-generated covers; the four-step induction)

> **Lemma 8.34.** *Let `A` be a complete strongly noetherian Tate ring and `U` a rational cover generated by a finite `T ⊆ A` with `T·A = A`. Then `U` is `𝒪_X`-acyclic.*

The induction (Wedhorn's (i)–(iv)):
- **(i)** For `f ∈ A` the single-element **Laurent cover** `U_f = {R(f/1), R(1/f)} = {x(f) ≤ 1} ∪ {x(f) ≥ 1}` is acyclic by Lemma 8.33, and stays acyclic on restriction to any rational subset. By Proposition A.3(3) and induction, every **Laurent cover** `V = U_{f₁} × ⋯ × U_{fᵣ}` (which is the rational cover generated by `T = {∏_{j∈J} fⱼ : J ⊆ {1,…,r}}`) is acyclic, and its restriction to any rational subset is acyclic.
- **(ii)** *Claim:* for finite `T = (f₀,…,fₙ)` generating `A` as an ideal, with `U` the cover it generates, there is a Laurent cover `(Vⱼ)` such that `U|_{Vⱼ}` is a cover by **units** of `𝒪_X(Vⱼ)`. *Proof:* for each `x` some `x(fᵢ) ≠ 0`, so by **Corollary 7.32** (Theorem 5.5) there is a unit `s ∈ A×` with, for all `x`, `x(s) < x(fᵢ)` for some `i`; the Laurent cover generated by `s⁻¹f₁,…,s⁻¹fᵣ` works.
- **(iii)** A rational cover generated by **units** `f₀,…,fₙ` is refined by the Laurent cover generated by `{fᵢ fⱼ⁻¹ : 0 ≤ i,j ≤ n}`.
- **(iv)** By (i)+(iii)+Proposition A.3(2), restrictions of unit-generated covers to rational subsets are acyclic. Then for a general `T`-generated `U` and the Laurent `V` from (ii): `U|_V` is acyclic (just shown) and `V|_U` is acyclic (by (i)), so Proposition A.3(1) transfers acyclicity from `V` to `U`. ∎

### Lemma 7.54 (the refinement that precedes 8.34)

> **Lemma 7.54.** *For a complete affinoid `A` and an open cover `(Vⱼ)` of `Spa A`, there exist `f₀,…,fₙ ∈ A` generating `A` as an ideal such that each `R(f₀,…,fₙ / fᵢ)` is contained in some `Vⱼ`.* (Wedhorn's port of [Hu3] Lemma 2.6.)

---

## 11. Appendix B — other auxiliary results (formalised, sorry-free; statements only)

The reviewer need not read these closely but may wish to spot-check the statements.

- **General `n`-variable restricted-power-series Tate topology** (Wedhorn Prop 6.21(2)): the topology on `Â⟨X₁,…,Xₙ⟩` with ring of definition `Â₀⟨X⟩` and ideal of definition `I·Â₀⟨X⟩`; proved a complete Tate topology with every ideal closed (Proposition 6.17 for it). This is the `C` of Theorem 5.6.
- **Example 6.39**: `Â⟨X, X⁻¹⟩ ≅ Â⟨X,Y⟩/(XY−1)` is a strongly noetherian Tate ring; supplies the `𝒪_X(U₁ ∩ U₂)` presentation in Lemma 8.33.
- **`μ_M` / `M⟨X⟩` apparatus** (Remark 8.29) and the canonical module topology (Remark 6.19): the concrete `{ϖⁿ M₀}` neighbourhood basis on a finitely generated module `M` (with `M₀` a finite `A₀`-submodule generating `M`).
- **Remark 7.30(2)**: for a Tate ring `A`, a finitely-generated ideal `T·A` is open iff `T·A = A` (used in Theorem 5.6 to make the `sᵢ` units).

---

## 12. Document metadata

- **Project**: Lean 4 / Mathlib formalisation of Wedhorn *Adic Spaces* Theorem 8.28(b).
- **Brief generated**: 2026-06-03 (supersedes the 2026-05-31 brief, whose open-mapping question is now resolved — Theorem 5.1).
- **Build status**: the project builds; the headline theorem is an honest assembly whose two fields reduce to the open leaves of §8. **No axioms are asserted** (every gap is an explicit `sorry`, not an `axiom`). The flatness/base-change/open-mapping/Nullstellensatz layers (§5) are sorry-free; several verified to depend only on Mathlib's classical foundations.
- **Open leaves on the critical path** (mathematical content, excluding the deferred Čech block): the Spa–completion injectivity (Prop 7.48 = [Hu2] 3.9, the one deep blocker, §8.1); the Remark 7.55 chain assembly (§6.2, bookkeeping); t.f.t. strong-noetherianity of presheaf values (§6.4); the topological inducing (downstream of acyclicity + the landed open mapping theorem, §8.2).
- **Deferred sub-project**: the Appendix-A Čech machinery + Lemmas 8.33/8.34 (~two dozen leaves, standard).
- **Recent activity**: a faithfulness-driven rebuild — a σ-compactness-free open mapping theorem ([He]), the `μ_M`/Lemma 8.31 layer, the general-`n` base-change noetherianity (Example 6.38), and migration of the whole chain off the false noetherian-ring-of-definition hypothesis (§8.3).
