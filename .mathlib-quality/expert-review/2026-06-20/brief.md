# Review brief #2 — the topological-embedding (inducing) step of affinoid sheafiness

*Prepared 2026-06-19 for an expert in adic spaces / non-archimedean geometry. Self-contained;
no repository access required. This follows up review #1 (the four residual leaves of Thm 8.28(b));
the new questions arose while implementing leaves #1 and #3.*

## 1. Goal and what has changed since review #1

We are formalising Wedhorn's Theorem 8.28(b): for a complete, strongly-noetherian Tate ring `A`
with ring of integral elements `A⁺`, the structure presheaf `𝒪_X` on `X = Spa(A, A⁺)` is a sheaf
of **topological** rings. By Remark 8.20 this reduces, for every finite covering of a rational
subset `U` by rational subsets `(Uᵢ)`, to two statements about the restriction map
`ρ : 𝒪_X(U) → ∏ᵢ 𝒪_X(Uᵢ)`:

- **(Embedding)** `ρ` is a topological embedding — injective *and* the topology on `𝒪_X(U)` is the
  subspace topology induced from the product;
- **(Gluing)** every overlap-compatible family in `∏ᵢ 𝒪_X(Uᵢ)` is in the image of `ρ`.

Since review #1 we have: (i) proved Proposition 7.41 (a height-1 analytic continuous valuation is
`≤ 1` on `A°`); (ii) reduced the non-open-prime Spa-point existence (leaf #3) to a single height-1
analytic-point leaf via 7.41; (iii) obtained the source [Hu2] and confirmed leaf #4 = [Hu2] Lemma
3.3(i) is hypothesis-free. Three questions remain, all about the **embedding** half and the
valuation-theoretic inputs.

## 2. Setting and the two competing formulations of "compatible family"

Notation: `𝒪_X(U) = Â⟨T/s⟩` is the completed rational localisation (a complete Tate ring); all
section rings here are complete Hausdorff topological rings with a countable basis of neighbourhoods
of `0` (a topologically nilpotent unit `ϖ ∈ A` is available). Write `R = 𝒪_X(U)` and
`S = ∏ᵢ 𝒪_X(Uᵢ)` (a finite product, hence again complete, Hausdorff, countably based).

We have **already proved injectivity** of `ρ : R → S`, and indeed the *algebraic* descent
statement, via faithfully flat descent (Stacks 023N): `R → S` is faithfully flat, and the descent
equalizer gives a ring isomorphism
```
        R  ≅  ker( S  ⇉  S ⊗_R S ),     s ↦ 1 ⊗ s − s ⊗ 1.
```
This identifies the *underlying ring* of `R` with the equalizer of the two coprojections into
`S ⊗_R S`. Crucially, this route uses **no pairwise intersections** `Uᵢ ∩ Uⱼ` — it works with the
single faithfully-flat extension `R → S` and the tensor square `S ⊗_R S`.

There is a second, classical formulation of the same equalizer — the **Čech** one:
```
        E  =  { (sᵢ) ∈ S : ρᵢⱼ(sᵢ) = ρⱼᵢ(sⱼ) in 𝒪_X(Uᵢ ∩ Uⱼ) for all i, j }  ⊆  S,
```
where `ρᵢⱼ : 𝒪_X(Uᵢ) → 𝒪_X(Uᵢ ∩ Uⱼ)` are the overlap restrictions. As sets, `E = ker(S ⇉ S⊗_R S)`
(both are "the compatible families"), and gluing says `image(ρ) = E`.

## 3. The obstruction we hit, and the established tools

We have, ready to use:
- **Banach's open mapping theorem, σ-compact-free form** (Wedhorn 6.16 / BGR §3.7.2): a continuous
  surjective `A`-linear map between complete, Hausdorff, countably-based topological `A`-modules is
  open. (We use the dilation-by-`ϖ` proof, so **no σ-compactness is needed** — important, since the
  Tate modules here are not σ-compact.)
- Faithfully flat descent (the displayed iso above), giving injectivity.

The clean route to **inducing** (the open half of "embedding") would be: corestrict `ρ` to the
equalizer `E`, get a continuous bijection `ρ̃ : R → E`; show `E` is **closed** in `S` (hence
complete); then Banach OMT makes `ρ̃` open, so `ρ̃` is a homeomorphism, and `ρ = (E ↪ S) ∘ ρ̃` is a
topological embedding.

The snag is **showing `E` is closed**. The Čech formulation makes this immediate: `E` is the
kernel of the continuous map `S → ∏ᵢⱼ 𝒪_X(Uᵢ ∩ Uⱼ)` into a Hausdorff target, hence closed. **But
this needs the pairwise intersections `Uᵢ ∩ Uⱼ` as honest affinoid/rational data, with their
Hausdorff section rings and the continuous overlap maps.** In our setting the rational pieces are
presented with *heterogeneous auxiliary data* — each `Uᵢ` carries its own ring/ideal of definition
`(A₀ⁱ, Iⁱ)` — and the only intersection construction we have produces `Uᵢ ∩ Uⱼ` *as rational data*
only when the two pieces share a common ring of definition (`A₀ⁱ = A₀ʲ`). For a general cover the
pieces do not share one. (The descent route was adopted precisely because it never forms pairwise
intersections.)

The descent formulation, on the other hand, gives `E = ker(S → S ⊗_R S)` — but `S ⊗_R S` carries
**no canonical ring topology**, so "kernel of a continuous map into a Hausdorff target" does not
apply, and we cannot conclude `E` closed this way.

## 4. Questions

**Q1 (primary — the inducing route).** What is the canonical proof that `ρ : 𝒪_X(U) → ∏ᵢ 𝒪_X(Uᵢ)`
is a topological **embedding** (not merely injective), for a complete strongly-noetherian Tate
ring, and does it require pairwise intersections? Concretely, which of these does an expert regard
as the right route?

- **(a) Descent-compatible inducing (no intersections).** Is there a way to see the equalizer
  `E = ker(S ⇉ S ⊗_R S)` as a **closed** subspace of `S` — and hence apply Banach OMT to `ρ̃ : R → E`
  — *without* introducing the pairwise intersections? For instance, does faithful flatness plus
  completeness already force `image(ρ)` closed in `S` (so that `ρ` is automatically a closed
  embedding), via some topological-descent or strictness argument that stays with the single
  extension `R → S`?
- **(b) The Čech route is genuinely needed.** If closedness really requires the overlap maps into
  `𝒪_X(Uᵢ ∩ Uⱼ)`, then we must build the pairwise-intersection-of-rational-subsets construction in
  full generality (heterogeneous rings of definition). Is that the expected cost, and is there a
  standard normalisation (pass to a common ring of definition for the whole finite cover) that makes
  this painless and is known to preserve the section rings up to topological isomorphism?
- **(c) The module-topology route (Wedhorn's own).** Does Wedhorn's proof of the embedding/inducing
  step in 8.28(b) actually go through Proposition 6.18 — i.e. via the *uniqueness of the topology on
  a finite module over a complete Tate ring* / the quotient-topology + open-mapping argument — rather
  than either descent or Čech overlaps? If so, what exactly is the finite-module input (`𝒪_X(U)` is
  not module-finite over anything obvious), and is 6.18 really the intended tool here?

We would like to commit to one route before building infrastructure; (a) would be ideal (it reuses
what we have), (b) is a clear but heavier build, (c) is what we would do if Wedhorn's own argument
is the module-topology one.

**Q2 (soundness — completeness in the non-open-prime point).** For an affinoid ring, is the
statement

> "for every non-open prime ideal `𝔭` of `A`, there is a continuous valuation `v` with
> `𝔭 ⊆ supp(v)` that is `≤ 1` on all power-bounded elements `A°`"

true **without** assuming `A` complete? Wedhorn's Lemma 7.45 (the source for this) assumes a
*complete* affinoid ring, and the construction uses completeness (via Prop 5.38, to place the ideal
of definition inside a maximal ideal). We only ever apply this at complete rings, but we would like
to know whether the completeness hypothesis is *essential* (so it must appear in the statement) or
removable — e.g. by transporting through `Spa(A) ≅ Spa(Â)` and applying 7.45 on the completion `Â`.

**Q3 (the height-1 input).** The remaining content of the non-open-prime point is the **height-1
vertical generalisation of a microbial valuation** (Wedhorn Remark 4.12 / 7.42(2)): an analytic
continuous valuation `v` is microbial, and one passes to a height-1 vertical generalisation `x`
(quotient by the largest proper convex subgroup), which is still continuous and has
`supp(x) ⊇ supp(v)`. Is there a clean, self-contained statement of "a microbial valuation has a
height-1 vertical generalisation" that reduces to a standard ordered-group / valuation-ring fact
(largest proper convex subgroup of a value group of finite rank, or minimal nonzero prime of the
valuation ring), suitable for formalisation — or is the cleanest path the blow-up / Krull–Akizuki
construction Wedhorn uses in the *noetherian* refinement?

## 5. References
- T. Wedhorn, *Adic Spaces* (arXiv:1910.05934): Thm 8.28, Rem 8.20, Prop 6.16/6.18, Lemma 7.45,
  Prop 7.41, Rem 4.12/7.42, Prop 5.38, Prop 7.48.
- R. Huber, *Continuous valuations*, Math. Z. 212 (1993): Lemma 3.3.
- Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §3.7 (Banach open-mapping).
- Stacks Project 023N (faithfully flat descent).
