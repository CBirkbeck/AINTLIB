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
