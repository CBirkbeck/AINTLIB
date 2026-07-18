# Worker decomposition — T-END0: the `End(E/S)` / degree / Hasse layer (KM Ch. 2 §§2.5–2.7)

*`/develop --decompose` first act for [T-END0] (tickets.md §v10.5). p0, 2026-07-08.
KM full text now in `refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf` (offset PDF = print + 11);
all quotes below transcribed verbatim. This is the G-lane resume artifact — the pieces close the
`aut_hom_eq_id_of_fullLevel` box (`Moduli/Groupoid.lean:125`) whose docstring already carries the
prose proof; here we source every step against KM and cut the leaves.*

## Goal (top-level result)

`aut_trivial_of_fullLevel` (Groupoid.lean:147) — an automorphism of `E/S` (`N ≥ 3` invertible)
fixing a naive full level-`N` structure is the identity — which the file already reduces (proven
categorical wrapper) to the **scheme-morphism core**:

    aut_hom_eq_id_of_fullLevel (N ≥ 3) (hinv : NIsInvertible S N) (E) (P Q : E.Section)
      (hPQ : E.IsNaiveFullLevel N P Q) (e : E ≅ E)
      (hP : P.1 ≫ e.hom.hom = P.1) (hQ : Q.1 ≫ e.hom.hom = Q.1) : e.hom.hom = 𝟙 E.E

**This is verbatim KM Corollary 2.7.2(1)** (Rigidity of level `N` structures): *"Let ε : E → E be an
automorphism … Suppose that ε induces the identity automorphism of E[N]. (1) If N ≥ 3, then ε = id."*
(print p.85, PDF 96). Consumers: T-G3 rigidity → T-E10 assembly, T-E9 rigid half, T-H6/T-H10.
T-W7-INDEPENDENT — genuine parallel stream.

## Prose proof (KM 2.7.2(1), matching the Groupoid box docstring)

Write `ε = e.hom.hom ∈ End(E/S)`. By hypothesis `ε` fixes `P, Q`; by **T-G2** rigidity (any pointed
`S`-endomorphism is a homomorphism — KM 2.5.1) `ε` is additive on points, and since `P, Q` generate
`E[N]` fibrewise (`IsNaiveFullLevel`) it induces the identity on `E[N] = ker[N]`. So `ε − 1` kills
`E[N]`, hence (KM 2.7.2 proof: *"ε−1 kills E[N], so it factors as ε−1 = g·N for some g ∈ End(E)"*)
`ε = 1 + [N]·g` for some `g ∈ End(E/S)` — **T-G3d**. Take degrees:

    deg(ε) = deg(1 + [N]·g) = 1 + N·tr(g) + N²·deg(g)          (T-G3b, from KM 2.6.3/2.6.2.2)
    tr(ε) = 2 + N·tr(g).

Since `ε` is an automorphism, `deg(ε) = 1`, so `N·tr(g) + N²·deg(g) = 0`, i.e. `tr(g) = −N·deg(g)`.
The discriminant inequality `tr(g)² ≤ 4·deg(g)` (**T-G3c**, KM 2.6.3(2)) gives `N²·deg(g)² ≤ 4·deg(g)`.
For `N ≥ 3` and `deg(g) ≥ 0` an integer this forces `deg(g) = 0` — this is the **already-proven**
`gme_deg_trace_forces_zero` (Groupoid.lean:88–103, sorry-free `nlinarith`). Finally positive-
definiteness of `deg` (**T-G3e**, KM 2.6.3(2) proof `deg(n−mf) ≥ 0`) gives `g = 0`, so `ε = 1`. ∎

## Sources (verbatim, banked)

**KM 2.5.1** (print p.77, PDF 88): *"The above structure of S-group-scheme on E/S is the unique
structure … for which '0' is the origin. If E and E′ are two elliptic curves over S, any S-morphism
f : E → E′ with f(0) = 0 is a homomorphism."* → the ring `End(E/S)` is a ring of homomorphisms +
**T-G2** (pointed ⟹ hom). Dual defined in the proof (print p.79): *"f^t = Pic(f) = f^* :
Pic⁰_{E′/S} → Pic⁰_{E/S} … via Abel's isomorphism … an S-homomorphism f^t : E′ → E."* (Abel iso
E ≅ Pic⁰ is KM §2.1 = **T-A6**.)

**KM 2.6.1** (print p.81, PDF 92): *"f^t f = deg(f) =: { N if f is an isogeny of degree N; 0 if
f = 0 }."* → the **master definition** of `deg : End(E/S) → ℤ` via `f^t ∘ f = [deg f]`.
**Cor 2.6.1.1** (print p.82): *"If f is an isogeny of degree N, so is f^t and f^{tt} = f"*, with
displayed *"deg([N]) = N²"*. **Thm 2.6.2** (print p.82): *"(f+g)^t = f^t + g^t"* (dual additive).
**Cor 2.6.2.1** (print p.83): *"the transpose of [N] is [N] itself."* **Cor 2.6.2.2** (print p.84):
*"there exists an integer, trace(f), such that f + f^t = trace(f)"*, proof *"deg(1+f) = 1 + deg(f) +
(f+f^t)."* **Thm 2.6.3** (print p.84): *"(1) f is a root of X² − trace(f)X + deg(f) = 0. (2)
(trace(f))² ≤ 4 deg(f)"*, proof *"deg(n − mf) ≥ 0."* **Cor 2.6.4** (print p.84): Hasse bound
*"|#E(F_q) − (q+1)| ≤ 2√q"*, via *"#E(F_q) = deg(1−F) = 1 + q − tr(F)."*

**KM 2.7.2** (print p.85, PDF 96) — the top-level: *"Let ε : E → E be an automorphism … Suppose ε
induces the identity of E[N]. (1) If N ≥ 3, then ε = id. (2) If N = 2, then ε = ±id."* proof:
*"ε−1 kills E[N], so it factors as ε−1 = g·N for some g ∈ End(E). Then ε = 1 + gN, so trace(ε) =
2 + N trace(g); deg(ε) = 1 + N trace(g) + N² deg(g). But deg(ε) = 1, and |trace(ε)| ≤ 2. So
|N trace(g)| ≤ 4, N trace(g) = −N² deg(g), i.e. |N² deg(g)| ≤ 4."* (Cor 2.7.1: automorphisms have
`tr ∈ {0,±1,±2}`; Cor 2.7.3/2.7.4 = the Γ₁(N) analogues for a rank-N subgroup / ℤ_N / μ_N.)

**GME §B8/§B9** (`decomposition-gme2.md`): B8 `f^t : E′→E` from `f^* : Pic⁰→Pic⁰` + Abel;
B9 (Hasse 2.6.10) `Tr f = f + f^t ∈ ℤ`, `f² − (Tr f)f + deg f = 0`, `Tr(ε)² < 4 ⟹ n ≥ 3 forces
deg g = 0 ⟹ g = 0`. **Fibre anchor to IMPORT (never re-prove)** — HasseWeil:
`Foundation/DegreeQuadraticForm.lean` (`degree_quadratic_closed`, `trace_identity_of_dual_chain`,
`degree_quadratic_genuine_addIsog`, `degree_quadratic_nonneg_of_witness`) + `HasseBound.lean`
(`hasse_bound`, `hasse_bound_unconditional`).

## Lean substrate (the real API this builds on)

`End(E/S) := E.asOver ⟶ E.asOver` (Over-`S` self-morphisms). Its **additive** group is the
MULTIPLICATIVELY-spelled `Hom.commGroup`: group-`1` = zero morphism (ring `0`), group-`*` = pointwise
sum (ring `+`), `f ^ n` = `[n]·f`, `mulBy n = (𝟙 E.asOver) ^ n = [n]` (GroupLaw.lean:86). Ring-`1` =
`𝟙 E.asOver`, ring-`*` = composition `≫`. The additive/multiplicative spelling is the one care-point;
the skeleton fixes it once by introducing `AddCommGroup`/`Ring (End E)` via `Additive.ofMul` on
`Hom.commGroup` + `≫` (biadditivity of `≫` = **END0-ring** infra leaf). `gme_deg_trace_forces_zero`
(the `nlinarith` closing `N ≥ 3 ∧ n·d = −n²d² bound ⟹ d = 0`) is ALREADY PROVEN (Groupoid.lean:88).

## Ordered lemma decomposition (leaves, with intended signatures)

1. **[T-END0a] `End(E/S)` ring** — `instance : Ring (End E)` (or `Semiring`+`AddCommGroup`): `+` =
   `Hom.commGroup` (additivised), `*` = `≫`, distributivity = biadditivity of composition over the
   pointwise group law. Source: KM 2.5.1 (endomorphisms are homs, closed under `+` and `∘`). *Infra;
   no KM-degree content.*
2. **[T-END0b] `endDeg : End E → ℤ`** (DS-data) + **`endDual : End E → End E`** (DS-data, `f^t`) with
   the pin `endDual f ≫ f = mulBy (endDeg f)` (KM 2.6.1) and `endDeg 0 = 0`, `endDeg 1 = 1`,
   `endDual (endDual f) = f`, `endDual` additive (KM 2.6.1.1/2.6.2). DS-register: docstring = KM 2.6.1,
   ticket = this, pins = the spec lemmas.
3. **[T-END0c] `deg_mulBy : endDeg (mulBy N) = N ^ 2`** (KM 2.6.1.1 displayed; fibre anchor
   HasseWeil `mulByInt_degree`/BB-DEG via T-B6). Also `endDual_mulBy : endDual (mulBy N) = mulBy N`
   (KM 2.6.2.1).
4. **[T-END0d] `endTrace : End E → ℤ`** := via `f + endDual f = mulBy (endTrace f)` (KM 2.6.2.2), and
   `trace_spec : endDeg (1 + f) = 1 + endDeg f + endTrace f`.
5. **[T-G3b] deg-quadratic expansion** — `endDeg (1 + mulBy N * g) = 1 + N * endTrace g + N^2 * endDeg g`
   (specialisation of KM 2.6.3(1)/2.6.2.2 with the bi-additive polarization of `endDeg`). *The
   `deg(1+N•g)` line of the box.*
6. **[T-G3c] Hasse / discriminant bound** — `endTrace g ^ 2 ≤ 4 * endDeg g` (KM 2.6.3(2)), fibrewise
   via T-RED0 + HasseWeil `hasse_bound`/`degree_quadratic_closed` transfer. *IMPORT, never re-prove.*
7. **[T-G3d] N-divisibility** — `ε` fixes `E[N]` (i.e. `ε − 1` kills `ker[N]`) `⟹ ∃ g, ε = 1 + mulBy N * g`
   (KM 2.7.2 proof, "ε−1 = g·N"). Needs the E[N] = ker[N] factoring (Torsion.lean `torsionι`).
8. **[T-G3e] positive-definiteness** — `endDeg g = 0 → g = 0` (KM 2.6.3(2) proof `deg(n−mf) ≥ 0`,
   sharpened to definiteness for the endomorphism ring of an elliptic curve).
9. **[T-G2] rigidity** — `isMonHom_of_one_comp_eq` (Rigidity.lean, sorried): pointed `S`-endomorphism
   is a homomorphism (KM 2.5.1). Already a separate ticket; consumed here.
10. **close `aut_hom_eq_id_of_fullLevel`** — wire T-G2 (→ ε additive → fixes E[N]) + T-G3d (→ `ε=1+N g`)
    + T-G3b (→ `deg ε = 1 + N tr g + N² deg g`) + `deg ε = 1` + T-G3c + `gme_deg_trace_forces_zero`
    (→ `deg g = 0`) + T-G3e (→ `g = 0`) → `ε = 1`. The arithmetic glue is DONE.

## Skeleton file

`ModularCurves/EllipticCurve/EndomorphismDegree.lean` (new; imports `EllipticCurve.GroupLaw`,
`EllipticCurve.Torsion`, HasseWeil degree/Hasse). States 1–8 as `:= by sorry` / DS-data defs that
`lake build` clean (DS-register rule for the `endDeg`/`endDual`/`endTrace` data sorries). Placement:
new file keeps it off the hot W7/GroupLaw lanes. `[CLEANUP-END]` after T-G3b+d+c per v10.5.

## Leaf tickets → board

T-END0a (ring), T-END0b (deg+dual DS-data), T-END0c (deg[N]=N²), T-END0d (trace), T-G3b, T-G3c,
T-G3d, T-G3e. Work order (v10.5): **T-END0a → b → c/d → T-G3b → T-G3d → T-G3c → T-G3e → close box**.
