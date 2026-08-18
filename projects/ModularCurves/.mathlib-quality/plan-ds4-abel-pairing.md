# Development Plan: DS4 — the relative Weil pairing via Katz–Mazur

Written 2026-08-05 after eleven `--decompose` rounds. Supersedes the route sections of
`Picard/SelfAdjointN.lean` and retires route β, the seesaw route, the cube route and the `ℓ/v` route.

## Goal

Discharge the seven `sorry`-roots of the DS4 register in `WeilPairing/Basic.lean` — `weilPairing` (`:49`),
`weilPairing_over` (`:53`), `_add_left` (`:111`), `_add_right` (`:122`), `_self` (`:202`),
`_nondegenerate` (`:270`), `_mul` (`:328`) — for an **arbitrary base scheme `S`** and **arbitrary `N`**,
by transcribing Katz–Mazur §2.8.1 and §2.8.5.

## References (all local, all read; page numbers are book pages)

| ref | used for |
|---|---|
| Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, **Thm 2.1.2** (Abel), pp. 63–67 | the leaf, and (2.8.1.7) |
| — **Lemma 1.2.7**, p. 11 | degree-one divisor is a section |
| — **§2.8.1**, pp. 87–89 | the pairing construction |
| — **§2.8.2–2.8.5**, pp. 89–90 | perfectness, alternation, `e_N` |
| Mumford, *Abelian Varieties*, **p. 53 Cor. 3** | `R¹f_*=0 ⟹ f_*` locally free + base-change compatible, **explicitly reduced-free** |
| — **p. 51 Lemma 1** | the *reduced*-base statement — **not** to be used; this is where the `k[ε]/(ε²)` failure lives |

## The chain, end to end

```
[A] degree-one cohomology + base change for arbitrary L      ← the one genuinely new package
      ↓
[B] natural Abel equivalence  E(T) ≃ Pic⁽¹⁾(E_T/T)            (KM 2.1.2, pp. 64–67)
      ↓
[C] the LEAF: exists_invertible_tensor_idealModule_add        (SelfAdjointN.lean:267)
      ↓   [already derived in-tree]
    (★) picMap_mulByHom_kappa_pow, (★′) picMap_mulByHom_kappa_eq_one
      ↓
[D] KM 2.8.1's pairing, specialised to π = [N]                 (pp. 87–89)
      ↓
[E] e_N as a scheme morphism + the register's specs            (2.8.5; Yoneda)
```

## What is already proved, and must not be rebuilt

| KM step | in-tree |
|---|---|
| `f_*𝒪_E = 𝒪_S` universally | `UniversallyOConnected` (`EllipticCurve/Rigidity.lean:54`), supplied by `locallyWeierstrass_pushforward_O_eq_O` (`PoleFiltration.lean:3000`) |
| **(2.8.1.6)** `H⁰(E, K_E^×) = {1}` | **`eq_one_of_pullback_eq_one`** (`EllipticCurve/SectionRigidity.lean:83`) — "a function trivial along the zero section is trivial". Sorry-free. |
| KM 2.1.2 step (c), noetherian approximation | `Picard/InvertibleSheafNoetherianSmoothStage.lean:257`, `ForMathlib/NoethApprox.lean` |
| KM 2.1.2 step (f), degree-one divisor ⟹ section | **mathlib** `Scheme.Hom.isIso_iff_finrank_eq` (`AlgebraicGeometry/Morphisms/FlatRank.lean:273`) |
| carried-vs-Abel group-law comparison | **`grpObj_mul_unique`** (`EllipticCurve/RecordGroupUnique.lean:414`), sorry-free |
| group object from a representable group-valued presheaf | **mathlib** `CommGrpObj.ofRepresentableBy` (`CategoryTheory/Monoidal/Cartesian/CommGrp_.lean:34`) |
| normalized-cocycle glue (the `K^×` layer KM 2.8.1 needs) | `Picard/GlueTrivialization.lean:98`, `Picard/RigidDescent.lean:65`, `Picard/InvertibleSheafCocycle.lean:44` |
| `(★)`, `(★′)` from the leaf | `Picard/SelfAdjointN.lean:490`, `:497` |

## Two scope reductions, both justified from the source

1. **`π = [N]` only.** KM 2.8.1 is stated for a general `N`-isogeny `π : E → E'` with dual `π^t`. DS4 needs
   only `e_N`, which is 2.8.5's case `π = [N]`, **self-dual by KM 2.6.2.1**. Taking `π = π^t = [N]` and
   `E' = E` removes the entire dual-isogeny theory from the critical path. With that specialisation,
   (2.8.1.7) reads `E[N](S) = Ker([N]^* : Pic⁰(E/S) → Pic⁰(E/S))`, and the `⊆` direction **is** `(★′)`.
2. **Boxes 2/3/4 of the July fence are off the path.** `relative-duality-genus-one` is used only in KM
   §2.2, *after* 2.1.2; `relative-Picard` representability is not used at all (KM's `Pic⁽¹⁾` is a set of
   iso classes mod `f^*`); no Poincaré bundle appears in pp. 63–90. Verified independently by me from the
   pages and by the second opinion. **This is a deliberate, recorded narrowing of the July reviewer's
   list, not a drift** — the list was scoped for the full canonicity project, which DS4 does not need.

## Generality decisions

* Arbitrary `S`, arbitrary `N` — no invertibility of `N`, no reducedness, no normality. KM 2.1.2 and
  2.8.1 are both stated over an arbitrary base, and Mumford p. 53 Cor. 3 is explicitly reduced-free. Any
  reappearance of a reducedness hypothesis is a signal that the route has drifted back to the seesaw.
* `[A]` is stated for an arbitrary fibrewise-degree-one invertible sheaf, **not** for `𝒪(n[0])`.
  Specialising to `𝒪([0])` and identifying a general `L` with it via relative Abel is **circular** — Abel
  is what `[B]` proves.
* The pairing is constructed group-law-free first (`abelSum`), then compared to the carried law via
  `grpObj_mul_unique`. Stating it directly in terms of `E.grp` re-introduces the circularity.

## Known traps (each already cost this session a false leaf or a wrong route)

1. **Never substitute a numerical consequence for a geometric hypothesis.** `h⁰ = 1` does not imply
   fibrewise triviality (`𝒪_E(P)`, `deg 1`, has `h⁰ = 1`); Čech exactness in positive degrees is false for
   the trivial sheaf on a genus-one fibre (`H¹(E,𝒪) = k`). Both are in `b2_log.jsonl`.
2. **`picRel = ker(0^*)` is strictly larger than `Pic⁰`** — over a field it carries every degree. It must
   never be the target of an Abel isomorphism. (Said independently by `SelfAdjointN.lean`'s docstring and
   by the second opinion.)
3. **Grep the conclusion, in the route's own vocabulary, before building anything.** Four times this
   session the tree already contained the target.

---

## Reference acquisition (2026-08-05) — all three gaps closed

Resolved from KM's own bibliography (book pp. 511–513), then obtained. **All live in `refs/ModularCurves/`,
which is a symlink to the main checkout's `refs/`, gitignored at `.gitignore:12:/refs` — verified invisible
to git in this worktree. Never commit them.**

| ref | citation | status |
|---|---|---|
| `[K-5]` | Katz, N., *Serre-Tate local moduli*, in **Surfaces Algébriques**, Springer LNM **868** (1981), 138–202 | **downloaded** `katz-serre-tate-local-moduli.pdf` (65 pp. = pp. 138–202, so pdf page = book page − 137); §5.0.1 and §5.2 **read** |
| `[Oda]` | Oda, T., *The first de Rham cohomology group and Dieudonné modules*, **Ann. Sci. ÉNS** 4e sér. **2** (1969), 63–135 | **downloaded** from NUMDAM, `oda-de-rham-dieudonne-1969.pdf` |
| Notes Added in Proof | KM, *Notes on Chapter 2*, book p. 505 | **read** |
| `[Mum 4]` | Mumford, *Abelian Varieties*, OUP 1970 | already local, already read |

### AP-D3 is cheaper than the citation suggests — and needs no hypothesis

Katz **Lemma 5.0.1** (p. 185), verbatim:

> "If `Pic(S) = 0` (e.g. **if `S` is the spectrum of a local ring**) the inclusion `K^× ⊂ (𝒪_X)^×` induces
> an isomorphism `Pic(X/S) = H¹(X, K^×) ⟶ H¹(X, 𝒪_X^×) = Pic(X)`."
> **"PROOF. Obvious from the long cohomology sequences."**

Note the hypothesis `Pic(S) = 0`. But that hypothesis is needed only for the *second* identification. From
the short exact sequence `1 → K^× → 𝒪_X^× → x_*(𝒪_S^×) → 1` the long sequence reads

`Γ(X,𝒪_X^×) → Γ(S,𝒪_S^×) → H¹(K^×) → Pic(X) → Pic(S)`,

and `f_*𝒪_X = 𝒪_S` (our `UniversallyOConnected`) makes the first map an isomorphism, giving

`1 → H¹(X, K^×) → Pic(X) → Pic(S)`,  i.e.  **`H¹(X, K^×) ≅ ker(0^* : Pic(X) → Pic(S))`**

with **no hypothesis on `Pic(S)`**. And `ker(0^*)` is exactly the tree's `picRel`
(`Picard/RelativePic.lean:57`). So AP-D3 in the form we need is the five-term sequence plus
`UniversallyOConnected` — not a citation-transcription. Katz's `Pic(S) = 0` enters only if one wants
`H¹(K^×) ≅ Pic(X)` itself, which we do not.

### A sign convention that must be fixed before AP-D6

Katz §5.2 (pp. 186–187) gives the same construction and ends with

> "`e_N(Y, λ) =` the global section of `𝒪_S^×` given locally by **`1/f_i(Y)`**."

while KM p. 89 defines `⟨P,P'⟩_π = "h(P)"` and says explicitly it is *"the **opposite** of [K-5, §5]"*.
**The two sources differ by inversion.** The formalisation must pick one and state it; `AP-D6`'s ticket now
carries this. Getting it wrong flips `e_N` to `e_N^{-1}`, which is invisible in the alternating and
bilinearity specs and only shows up in the determinant/Galois compatibilities downstream.

### `_self` is not a sibling of `_mul` — it DEPENDS on it

KM, Notes on Chapter 2, p. 505, gives a complete proof of `e_N(R,R) = 1`:

> "Let `E/S` be an elliptic curve, `N ≥ 1` and `M ≥ 1` two integers, and `P, Q ∈ E[NM](S)`. Then we have
> `(e_{NM}(P,Q))^M = e_{NM}(MP, Q) = e_N(MP, MQ)`, the last equality by applying **(2.8.4.1)** … Taking
> `M = 2` and `P = Q`, we find `1 = (e_{2N}(P,P))² = e_N(2P, 2P)`, for `P ∈ E[2N](S)`, the first equality
> by **2.8.3**. Because `[2] : E → E` is f.p.p.f. surjective, any point `R` in `E[N](S)` is locally
> f.p.p.f. of the form `2P` for `P ∈ E[2N](S)`, whence we have `e_N(R,R) = 1` for `R ∈ E[N](S)`."

So `weilPairingEval_self` (`Basic.lean:202`) needs **2.8.4.1 — the composability formula, which is
`_mul`** — plus 2.8.3 (alternation) and f.p.p.f. descent along `[2]`. **The board had `_self` and `_mul`
as siblings; they are not.** Corrected below. Note also that the argument is genuinely f.p.p.f.-local, so
`_self` needs descent, not just a pointwise argument.

### Board corrections following the acquisition

* **AP-D3**: no longer blocked on an unavailable reference. Route is the five-term sequence; source quote
  is Katz Lemma 5.0.1 with the hypothesis-scope note above. **Status: ready.**
* **AP-D6**: gains the sign-convention obligation (KM is the opposite of Katz).
* **AP-E4 `_self`**: now sourced with a complete proof, and **re-blocked on AP-E6 `_mul`** rather than
  parallel to it. Additional input: f.p.p.f. surjectivity of `[2]` and descent.
* **AP-E5 `_nondegenerate`**: reference now in hand (`[Oda]`), but the substance is unchanged — Cartier–
  Nishi duality is absent from mathlib and this remains a sub-development, not a ticket.

**Readiness after acquisition**: AP-A1, AP-D1 and **AP-D3** can start now. One ticket (AP-E5) still needs
its own sub-development; no ticket is now blocked on an *unobtainable* reference.

---

## Consolidated architecture (2026-08-06, rounds 15–18 — supersedes groups A/B above)

Sources merged: Hida GME 2.2.1–2.2.2 (fibre computation; three source defects corrected, see
`decomposition-gme2.md` CORRECTIONS) + KM 2.1.2 pp. 64–67 (functoriality and the three repairs). (2.15)
`R¹f_*𝒪_E` is **off the critical path** — only the degree-one package matters, and both sources state it
identically.

1. **[A′] degree-one package, arbitrary invertible `L`** (KM p. 66 = Hida pp. 107–108): fibrewise
   `H¹ = 0` (Serre duality, `deg L⁻¹⊗Ω = −1 < 0`) and `h⁰ = 1` (RR) ⟹ `R¹f_*L = 0` and `f_*L` invertible,
   base-change compatible — via noetherian approximation + Mumford §5 L1/L2 (transcribed in
   `LowDegreeFiniteProjectiveReplacement.lean`) / GME 1.10.4. Fibre facts through the tree's Čech layer
   with **finite homology** (`orderedBaseCechHomologyFinite_of_isProper` + `BoundedFlatBaseChange`
   section), never the finite-terms section.
2. **[B′] relative Picard locality via zero-rigidification** — needs `UniversallyOConnected` +
   `eq_one_of_pullback_eq_one` (both proved). Hida's locality claim is repaired here, per KM p. 65.
3. **[B″] the evaluation-divisor inverse `D(L)`**, natural in `T` — replaces Hida's fibrewise-injectivity
   inference; endpoint is mathlib `isIso_iff_finrank_eq`. Gives injectivity + surjectivity at once, on all
   nilpotent thickenings.
4. **[C′] group law transported** by `CommGrpObj.ofRepresentableBy`; the Abel criterion is the tensor
   identity; comparison with the carried law by `grpObj_mul_unique` (proved) — Hida's uniqueness
   (Cor 2.2.5) is NOT formalised.
5. **[D/E] unchanged** from the board (KM 2.8.1 at `π = [N]` with **typed slots** via `λ_E`; sign pin KM
   = opposite of Katz [K-5]; `_self` re-decomposed: direct skew-symmetry from the two-slot construction →
   new `NM`-torsion composability (the registered `_mul` is a different statement) → fppf `[2]`-descent →
   diagonal; D5→E1 naturality-before-Yoneda obligation; `_nondegenerate` = Cartier–Nishi sub-development
   [Oda, in refs/]).

## STATUS: STABLE (2026-08-06, round 19)

Reviewer verdict on the consolidated chain: **"NO FURTHER MATHEMATICAL FLAWS FOUND."** Eight precision
pins recorded in `decomposition.md` round 19 — binding at implementation time; pin 1 corrects [C′]'s
normalisation: `I(D(L))⁻¹ ≅ L ⊗ f^*((f_*L)^∨)`, never `(0^*L)^∨`. Residual risk is engineering.
Next: `/develop --continue` to re-cut board groups A/B to [A′]–[D′] (groups D/E stand, with pins 2–8),
then `/beastmode` starting at [A′].
