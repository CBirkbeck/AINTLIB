# Decomposition — T-PIC0 + COH-1 stream (fable-PIC0, 2026-07-08)

*`/develop --decompose` artifact for the v10.11 stream claim. Sources read in full this
session from `refs/ModularCurves/`: **[GME]** Hida, *Geometric Modular Forms and Elliptic
Curves* (2001): §1.10 pp. 72–82 (all of 1.10.1–1.10.3 + Cor 1.10.5 + the §1.11 lead-in),
§2.2.1–2.2.2 pp. 107–110. **[Mum]** Mumford, *Abelian Varieties* (2nd ed. 1974): §5
"Cohomology and base change", pp. 46–55, read in full (main theorem, Lemma 1, Lemma 2,
Corollaries 1–6). Page cites below are book pages; PDF offset +10 (GME), +11 (Mum).*

## Skeleton location

- `ModularCurves/ForMathlib/BaseChangeKerCoker.lean` — COH-1 module core (leaves A1–A6).
- `ModularCurves/Picard/InvertibleSheaf.lean` — T-PIC0 stage P1 (leaves P1a–P1d + GAP-1).

Both files import mathlib only (no project imports): zero coupling to in-flight lanes.

## Route decisions (binding, with source justification)

### COH-1: Mumford-§5 module route, NOT Hida's own §1.10 proof

The pinned target (decomposition-gme2 header): *"COH-1 = GME Lemma 1.10.4
(cohomology-and-base-change exactness criterion for `T_i(F) = R^i f_*(L ⊗ f*F)`: `T₁`
exact ⟹ `T₀` exact; `f_*L` locally free with `(f_*L)⊗k(s) ≅ f_*(L(s))`)."*

**Hida's own proof of Lemma 1.10.4 (pp. 80–81, read in full) is NOT the route.** It
consumes his §1.10.2 facts (8) (coherence of `R^i f_*`, "[EGA], III. 3.2.1") and (9)
(theorem on formal functions, "[EGA], III.4.1.5"), plus Mittag-Leffler and faithful
flatness of adic completion ("[CRT] Theorem 8.14"). Verbatim, from the p. 80–81 proof:

> "Since f is proper, T_i(A) is of finite type. Thus T_i(A) ⊗ M/m_A^n M is of finite
> length, and hence Ker(φ_n) is of finite length. Fix n. Then the image of Ker(φ_N)
> under the natural projection in Ker(φ_n) is stationary as N → ∞, that is, the
> Mittag-Leffler condition [ALG], II.9. Thus the projective limit of φ_N is surjective.
> That is, by (9) [the formal-functions display follows]"

Coherence + formal functions are absent from mathlib, explicitly B3-scale (EGA III
developments), and adjacent to the owned COH-3 mathlib lane ("do not build cohomology
foundations" — ecosystem survey line 15). Per the source-faithfulness escalation rule
("the step needs substantial infrastructure absent from mathlib ⟹ the source proves it
an easier way — cross-reference other sources"), the route of record is the source Hida
himself cites for the lemma — **"Lemma 1.10.4 ([ALG], III.12.10)"** (p. 79) — i.e. the
Grothendieck-complex ("[Mum] §5 / Hartshorne III.12") machine: replace the cohomology
functor by a finite complex of finite projective modules; every base-change statement
becomes finite linear algebra. [Mum] p. 46, verbatim:

> "THEOREM. Let f: X → Y be a proper morphism of noetherian schemes with Y = Spec A
> affine, and 𝓕 a coherent sheaf on X, flat over Y. There is a finite complex
> K•: 0 → K⁰ → K¹ → ... → Kⁿ → 0 of finitely generated projective A-modules and an
> isomorphism of functors H^p(X ×_Y Spec B, 𝓕 ⊗_A B) ≅ H^p(K• ⊗_A B), (p ≥ 0) on the
> category of A-algebras B."

**Cut line (what is formalized now vs. deferred):** the *existence* of K• for a given
`f, 𝓛` is the geometric half — [Mum] proves it from a finite affine Čech cover ("Choose
a finite affine covering 𝔄 = {U_i} of X ... the Čech complex ... is a finite complex of
A-flat modules, whose cohomologies are isomorphic to the cohomology groups H^p(X,𝓕)",
p. 46) plus [Mum §5 Lemma 1]. That half needs scheme cohomology (`H^p`, Čech
comparison) = the owned mathlib COH-3 lane; it is **deferred as the named interface**:
consumers will instantiate `d : K⁰ →ₗ[A] K¹` as the Čech differential of the 2-chart
cover of a Weierstrass curve once that lane lands. The *criterion* half — everything
after K• exists — is pure module theory over a noetherian ring and is **fully
formalized now** (leaves A1–A6). For relative curves the complex has amplitude [0,1]
(one differential): Grothendieck vanishing in Hida's own application, p. 82: "T_n is
right exact (for n as in the theorem)"; n = 1 for curves. So the package is stated for
a single map `d : P →ₗ[R] Q` — the maximal-generality *module* statements; the
complex-indexed packaging is deliberately NOT built (it would duplicate the in-flight
mathlib homological lane's design space for zero consumer value today).

**Faithfulness of the [0,1] reduction to the pin.** The pin's three clauses map as:
- "T₁ exact ⟹ T₀ exact": GME p. 82, verbatim: *"If n = 1, T₁(𝓕) = T₁(O_S) ⊗_{O_S} 𝓕,
  and hence T₁ is an exact functor if R¹f_*𝓛 = T₁(O_S) is locally-free. In this case,
  T₀ is also exact."* — leaf **A4** (kernel–base-change under flat cokernel): "T₁(O_S)
  locally free" = `coker d` flat (finite locally free = finite flat = finite projective
  over any ring; over noetherian R these coincide — mathlib
  `Module.Flat.projective_of_finitePresentation`), and "T₀ exact" = `ker (d ⊗ M) ≅
  (ker d) ⊗ M` naturally in M.
- "f_*L locally free": Cor 1.10.5 (p. 82), verbatim: *"Corollary 1.10.5 Let the
  notation and the assumption be as in the theorem. Assume that n = 1, and let 𝓛 be an
  O_X-module locally free of finite rank. If R¹f_*𝓛 is locally O_S-free, then f_*𝓛 is
  also locally O_S-free."* — leaves **A5a/A5b** (`ker d` finite + projective).
- "(f_*L)⊗k(s) ≅ f_*(L(s))": the (2.15) application, GME p. 107: *"Again by Lemma
  1.10.4, we know f_*𝓛 is locally free and (f_*𝓛) ⊗ k(s) ≅ f_*(𝓛(s))."* — leaf **A4**
  at `M = k(s)` plus the algebra-form bridge **A6**.
- The vanishing-detection step feeding all of these (GME p. 107: *"Since (R¹f_*𝓛) ⊗
  k(s) ≅ H¹(E_s, 𝓛(s)) = 0 for all geometric points s ∈ S, we know that R¹f_*𝓛 = 0"*)
  — leaves **A1** (cokernel base change, the `i = n` right-exactness "T₁(𝓕) = T₁(O_S) ⊗
  𝓕" of p. 82) + **A2** (finitely generated module with all fibres zero is zero).

Hida's Lemma 1.10.4 itself, statement verbatim (pp. 79–80):

> "Lemma 1.10.4 ([ALG], III.12.10) Let the assumption be as in the theorem. Let i ≥ 0
> be an integer. Suppose that 𝓛 is locally free. Let s be a geometric point of S. Then
> the following two conditions are equivalent: (i) T_i over Spec(O_{S,s}) is right
> exact; (ii) ι is an isomorphism for all quasi-coherent 𝓕 on Spec(O_{S,s}). If either
> i ≥ dim(X ×_S Spec(O_{S,s})) or ι : T_i(O_S) ⊗_{O_S} k(s) → T_i(k(s)) is surjective
> for a given i, then (i) and (ii) hold."

The abstract (i)⟺(ii) equivalence for a general functor is functor-category material no
consumer uses; the criterion lands in the concrete ker/coker forms exactly where the
consumers use it ((2.15) p. 107, p. 82 passage, A7.b), per the decomposition-gme2
Lean-shape note ("stated with the COH-1 statements as explicit hypotheses-in-file").
The i ≥ dim clause = A1 (coker is the top of a length-1 complex); the surjectivity
clause at i = 0... is not consumed by any pinned chain (all consumers enter through
fibrewise H¹-vanishing, i.e. A1+A2 then A4); it is NOT cut as a leaf now — recorded as
an optional follow-up (`[Mum] Cor. 2` route) if a consumer ever needs it. Likewise
[Mum] Cor. 1 semicontinuity: out of pin, not cut.

### T-PIC0: X.Modules substrate; tensor-by-sheafification; group staged behind GAP-1

Board pin (v4 amendments): *"[T-PIC0] Pic(X) for a scheme via invertible O_X-modules
(mathlib `SheafOfModules` + LocallyFree ✓ merged); fibre-degree of an invertible
sheaf."* Source anchor GME 2.2.2 p. 108, verbatim:

> "We write E_T for E ×_S T and Pic(E_T) for the group of isomorphism classes of all
> invertible sheaves on E_T. Then we consider the following contravariant functors
> Pic_{E/S}, Pic^ν : SCH_{/S} → SETS for integers ν:
> Pic_{E/S}(T) = Pic(E ×_S T)/f_T^* Pic(T) for f_T : E ×_S T → T,
> Pic^ν_{E/S}(T) = [𝓛 ∈ Pic_{E/S}(E_T) | deg(𝓛(t)) = ν for t ∈ T]"

and the locality statement (2.17), p. 109, verbatim:

> "Pic¹ is local on S. (2.17) The formation of an invertible sheaf is local; thus, the
> obstruction, if any, comes from the equivalence relation "≈". Since we have the
> 0-section 0 : S ↪ E, we have a group homomorphism 0* : Pic(E) → Pic(S) for which f*
> is a section. Thus Pic(E) = Ker(0*) ⊕ Im(f*) and therefore Pic_{E/S} is actually a
> subfunctor of Pic_{/E}."

**Mathlib state (surveyed this session against the pin):**
- `CommRing.Pic R := Shrink (Skeleton <| SemimoduleCat.{u} R)ˣ` exists
  (`Mathlib/RingTheory/PicardGroup.lean`, Junyan Xu 2025) with `Module.Invertible`,
  `Pic.mk`, `mk_eq_mk_iff`, and a file TODO *"Connect to invertible sheaves on Spec R"*
  — the scheme-level Pic is confirmed absent and wanted upstream.
- `X.Modules := SheafOfModules X.ringCatSheaf` exists
  (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`, Riou–Yang) — abelian; `Hom.app`,
  `pushforward/pullback f` with adjunction, `pullbackComp`, `pushforwardComp`.
- `PresheafOfModules` is monoidal for commutative-ring-valued `R`
  (`…/Presheaf/Monoidal.lean`): instance for `PresheafOfModules.{u} (R ⋙ forget₂ _ _)`;
  `X.ringCatSheaf.obj = X.sheaf.val ⋙ forget₂ CommRingCat RingCat` matches.
- **No monoidal structure on `SheafOfModules`** (no `Sheaf/Monoidal.lean`); the pattern
  exists for constant coefficients: `Mathlib/CategoryTheory/Sites/Monoidal.lean` gives
  `MonoidalCategory (Sheaf J A)` via `(J.W).IsMonoidal` + localization — the
  sheaf-of-modules analogue is the obvious next step of the same (Riou) lane.
- `SheafOfModules.unit`, `free I`, `IsLocallyFree` (Nugent 2026),
  `pullbackObjFreeIso`/`pullbackObjUnitToUnit` (iso for final site functors) exist.

**Decision:** define the tensor `M ⊗ N := sheafify (M.val ⊗ N.val)` (both ingredients
merged), `IsInvertible` by local triviality along an open cover (matching "the
formation of an invertible sheaf is local", and giving (2.17)'s Ker⊕Im arguments their
natural form later). The **group** `Pic X := (Skeleton X.Modules)ˣ`-style needs the
associativity/comm/unit isos of the sheafified tensor; their kernel is ONE compatibility:

**GAP-1 (explicit API gap, own sub-development):** *sheafification ⊗-compatibility on a
scheme's Zariski site* — for a presheaf-of-modules map that sheafifies to an iso (e.g.
the unit `η_Q : Q → sheafify Q`), `η_Q ⊗ id_P` sheafifies to an iso; equivalently
`sheafify ((sheafify Q) ⊗ P) ≅ sheafify (Q ⊗ P)`, and restriction-to-opens commutes
with sheafification. Candidate routes (to be chosen by a dedicated `/develop` pass
before any GAP-1 ticket is worked): (a) mathlib's `J.over U`-machinery (the route
`Sheaf/LocallyFree.lean` already walks); (b) stalk functors + enough points of the
Zariski site (filtered-colimit ⊗ commutation); (c) upstream coordination — this is
squarely the Riou lane's `Sites/Monoidal.lean` pattern applied to `PresheafOfModules`'s
locally-bijective `W`; check mathlib4 open PRs before building (ecosystem discipline).
GAP-1 blocks: the Pic group law (P2), tensor-preserves-invertible (P1b). It does NOT
block: tensor def, invertibility def, unit lemmas (P1a, P1c), pullback stability (P1d),
or anything in COH-1.

**Fibre degree** (T-PIC0's second clause): requires degree of invertible sheaves on
curves over fields — the decomposition-gme2 route note says "via pullback to fibres +
degree on curves-over-fields (HasseWeil divisor theory anchor)". Statements-only until
the anchor audit; cut as a scoping ticket (T-PIC-DEG0), not a skeleton leaf. (HasseWeil
has ClassGroup/Pic⁰ machinery per the ecosystem survey §3; whether its degree theory
matches the fibre-of-a-scheme packaging is exactly what the scoping ticket determines.)

## Result COH-1: the base-change criterion package (module core)

### Plain-English proof (from [Mum] §5, transcribed; specialised to one differential)

Let R be a (noetherian, where stated) commutative ring and `d : P →ₗ[R] Q` a map of
finite projective modules — the amplitude-[0,1] Grothendieck complex of a relative
curve, `T⁰(M) = ker (d ⊗ id_M)`, `T¹(M) = coker (d ⊗ id_M)`.

1. **Top-degree right exactness** ([Mum] p. 49 "using the cohomology sequence in
   reverse"; GME p. 82 "T_n is right exact"): tensoring is right exact, so cokernels
   commute with ⊗ always: `T¹(M) ≅ T¹(R) ⊗ M`. No hypotheses.
2. **Fibrewise vanishing detects vanishing** (GME p. 107 step "R¹f_*𝓛 = 0"): `T¹(R) =
   coker d` is finitely generated (Q is); a finitely generated module all of whose
   fibres `N ⊗ κ` vanish (κ ranging over residue fields, equivalently all R-fields) is
   zero — Nakayama at each prime, i.e. `Module.support_eq_empty_iff`.
3. **Purity from a flat quotient** ([Mum] Lemma 2's mechanism; Stacks 00HL-shaped):
   if `0 → N₁ → N₂ → N₃ → 0` is exact with N₃ flat, it stays exact (in particular
   left-exact) after `⊗ M` for every M. This is Tor₁(N₃, M) = 0, done Tor-free by the
   standard free-presentation diagram chase.
4. **Kernel base change under flat cokernel** (= "T₁ exact ⟹ T₀ exact", GME p. 82;
   [Mum] Cor. 2's splitting mechanism in module form): assume `coker d` flat. Then
   `im d ⊆ Q` has flat quotient, so (3) applied to `0 → im d → Q → coker d → 0` makes
   `im d ⊗ M → Q ⊗ M` injective; `im d` is itself flat (ideal criterion + (3), leaf
   A3); so (3) applied to `0 → ker d → P → im d → 0` makes `ker d ⊗ M → P ⊗ M`
   injective with image exactly `ker (d ⊗ M)` (right exactness of the first sequence
   under ⊗ + the injectivity just established). Hence the canonical map
   `(ker d) ⊗ M → ker (d ⊗ M)` is bijective, naturally in M.
5. **Local freeness of the kernel** (Cor 1.10.5): over noetherian R with `coker d`
   flat: `im d` is finite (submodule of finite Q over noetherian) and flat, hence
   finitely presented and thus projective; `0 → ker d → P → im d → 0` splits; `ker d`
   is a direct summand of the finite projective P, hence finite projective (= locally
   free of finite rank).
6. **Fibre identification** ((2.15): `(f_*𝓛) ⊗ k(s) ≅ f_*(𝓛(s))`): the map in (4) at
   `M = k(s)`, rewritten through the `LinearMap.baseChange` form for an R-algebra A:
   `A ⊗ ker d ≅ ker (d.baseChange A)` — pure `AlgebraTensorModule` bookkeeping over (4).

### Lemmas (in order; Lean declarations in `ForMathlib/BaseChangeKerCoker.lean`)

- **A1** (leaf, mathlib-adjacent): `cokerLTensorEquiv` — `M ⊗ (Q ⧸ range d) ≃ₗ
  (M ⊗ Q) ⧸ range (d.lTensor M)`, naturally.
  - Source: [Mum] p. 49 (Lemma 2 proof, "using the cohomology sequence in reverse" —
    top-degree case); GME p. 82: verbatim *"Since T_i(𝓕) = R^i f_*(𝓛 ⊗_{O_X} f*𝓕), T_n
    is right exact (for n as in the theorem) if 𝓛 is locally free. If 𝓛 = O_X, then
    T₀(O_S) = f_*(O_X)"* and p. 107: *"⊗k(s) comes out of the functor f_*"* (the
    displayed exact sequence of k(s)-spaces).
  - Lean ↔ source: right-exactness of ⊗ makes the top cohomology of `[P → Q] ⊗ M`
    equal `coker(d) ⊗ M`; this is the "T₁(𝓕) = T₁(O_S) ⊗ 𝓕" clause verbatim, in module
    form with `T₁(R) = Q ⧸ range d`.
  - Discharge: mathlib `TensorProduct.tensorQuotientEquiv` /
    `TensorProduct.quotientTensorEquiv` (`Mathlib/LinearAlgebra/TensorProduct/
    Quotient.lean:105,131` — verified present in the pin) composed with
    `range (d.lTensor M) = map (range d)`-style identities
    (`Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean` has the
    `lTensor`-range/exactness toolkit). ≤ 3-lemma composition expected; if the submodule
    bookkeeping bloats, it stays a small self-contained construction.
  - Attacks attempted:
    - [1] Counterexample search: cokernels/⊗: right-exactness of tensor is
      unconditional (`rTensor_exact` in the pin); no hypothesis to violate. No
      contradicting lemma found (RightExactness.lean asserts the positive).
    - [2] Edge cases: `d = 0` ⟹ both sides `M ⊗ Q` ✓; `d` surjective ⟹ both sides `0` ✓;
      `M = R` ⟹ identity up to `lid` ✓.
    - [3] Hypothesis test: no flatness/finiteness used — correct, tensor is right
      exact over any ring, matching [Mum] Lemma 2's "any A-algebra B" generality
      (stated for modules, strictly more general than algebras).
    - [4] Source-drift: GME's T₁-clause is for `𝓛` locally free; the module statement
      needs nothing — the locally-free hypothesis in GME feeds the *flatness of the
      Čech terms* (K•-existence side), not this step. No drift: the criterion half
      never uses it.
    - [5] Discharge attack: `tensorQuotientEquiv`/`quotientTensorEquiv` verified
      present at the cited file/lines this session (grep). Exact statement-shape check
      deferred to proof time as noted.
    - Verdict: SURVIVED (5 categories).
  - Prior-B2: no name/shape match (log read this session; 1 real entry: T-A4
    `isWeierstrassModel_unique`, unrelated).

- **A2** (leaf, mathlib): `subsingleton_of_forall_field_tensor` — finitely generated N
  with `K ⊗[R] N` trivial for every R-field K (in particular every residue field) is
  trivial.
  - Source: GME p. 107, verbatim: *"Since (R¹f_*𝓛) ⊗ k(s) ≅ H¹(E_s, 𝓛(s)) = 0 for all
    geometric points s ∈ S, we know that R¹f_*𝓛 = 0."* (The "geometric points"
    quantifier = all field-valued points, which is why the leaf quantifies over
    R-fields; each prime's residue field is one.)
  - Lean ↔ source: with `N := coker d` f.g. (leaf A1 makes `(R¹f_*𝓛)⊗k(s) =
    coker(d)⊗k(s) = coker(d ⊗ k(s))`), the quoted inference is exactly "all fibres
    vanish ⟹ N = 0".
  - Discharge: `Module.support_eq_empty_iff` (`Mathlib/RingTheory/Support.lean:119`,
    verified) + the f.g. Nakayama bridge `N ⊗ κ(𝔭) = 0 ⟹ N_𝔭 = 0`
    (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`-style; also reachable via
    `Module.rankAtStalk_eq_zero_iff_notMem_support`, FreeLocus.lean:290 — flat-free
    fallback to be picked at proof time).
  - Attacks attempted:
    - [1] Counterexample search for non-f.g.: ℚ over ℤ has all fibres ℚ⊗κ(p)... ℚ⊗𝔽_p =
      0 and ℚ⊗ℚ = ℚ ≠ 0 — fibre at (0) nonzero, hypothesis fails, consistent. Better:
      ⊕_p 𝔽_p? fibre at (0) is 0, at p is 𝔽_p ≠ 0 — fails hypothesis. An R-module with
      ALL field fibres 0 and N ≠ 0 must be non-f.g. with empty support — impossible
      (support of nonzero module nonempty? FALSE for non-f.g.? e.g. ℚ/ℤ over ℤ: fibres
      (ℚ/ℤ)⊗𝔽_p = (ℚ/ℤ)[p]/p(...) hmm = ℚ/ℤ ⊗ ℤ/p = (ℚ/ℤ)/p(ℚ/ℤ) = 0 (divisible), and
      ⊗ℚ = 0 (torsion) — ALL field fibres vanish yet ℚ/ℤ ≠ 0.) **Attack succeeded
      against the field-fibre form without f.g.** — the `Module.Finite` hypothesis is
      load-bearing; kept, and the docstring records the ℚ/ℤ counterexample.
    - [2] Edge cases: N = 0 ✓; R a field: hypothesis at K = R gives N = 0 ✓; R local:
      only κ(m) needed — consistent with NAK.
    - [3] Hypothesis test: f.g. necessary (attack [1]); quantifying over all R-fields
      vs. all residue fields: equivalent under f.g. (support argument), all-fields form
      chosen since consumers have geometric points (fields, not just residue fields).
    - [4] Source-drift: GME concludes from geometric fibres; a geometric point s maps
      to some 𝔭 with k(s) ⊇ κ(𝔭) faithfully flat over κ(𝔭), so vanishing at k(s) forces
      vanishing at κ(𝔭) — the all-R-fields hypothesis is implied by GME's; no drift.
    - [5] Discharge: `Module.support_eq_empty_iff` verified in pin (grep, line 119);
      NAK lemma name to be pinned at proof time (two candidate routes recorded).
    - Verdict: SURVIVED, with hypothesis hardening from attack [1] (f.g. required).
  - Prior-B2: no match.

- **A3** (leaf, ours; Stacks 00HL-shaped): `Module.Flat.lTensor_subtype_injective_of_flat_quotient` — N ⊆ Q with `Q ⧸ N` flat ⟹
  `N.subtype.lTensor M` injective for all M (purity of the inclusion).
  - Source: [Mum] p. 49 Lemma 2, verbatim: *"Then it is easy to see that all the
    modules Z^p = Ker(L^p → L^{p+1}) are flat too, hence 0 → Z^p → L^p → Z^{p+1} → 0 is
    a short exact sequence of flat A-modules. Therefore 0 → Z^p ⊗_A B → L^p ⊗_A B →
    Z^{p+1} ⊗_A B → 0 is exact"* — the mechanism "SES with flat outer terms stays exact
    under ⊗" ; the sharp form needs only the QUOTIENT flat (Tor₁(N₃,·) = 0), which is
    the form [Mum]'s "it is easy to see … flat too" implicitly runs through (his Z^{p+1}
    is the flat quotient). Cross-reference: Stacks 00HL ("if N₃ is flat the sequence
    remains exact upon tensoring").
  - Lean ↔ source: `Function.Injective (N.subtype.lTensor M)` is the left-exactness
    clause of the quoted display for the SES `0 → N → Q → Q/N → 0`.
  - Discharge status: **not found in the pin** (Flat/Basic has `lTensor_exact` for the
    tensored-in module flat — the other variable; Flat/Stability has no SES lemma —
    grepped this session). Genuine but small gap: Tor-free proof via free presentation
    `F ↠ M` and the 3×3 chase, ~40–60 LOC (source spends 6 lines, p. 49). Upstream
    candidate. Five-method search re-run mandatory at proof start (G2), incl. loogle
    `Module.Flat ?Q → Function.Injective (LinearMap.lTensor ?M ?f)` variants.
  - Attacks attempted:
    - [1] Counterexample without flat quotient: `N = 2ℤ ⊆ ℤ = Q`, M = ℤ/2: `2ℤ ⊗ ℤ/2 →
      ℤ ⊗ ℤ/2` sends 2⊗1 ↦ 2⊗1 = 0 while 2⊗1 ≠ 0 in 2ℤ⊗ℤ/2 (≅ ℤ/2) — non-injective, and
      Q/N = ℤ/2 is not flat ✓ hypothesis is sharp.
    - [2] Edge: N = Q (quotient 0 flat) ⟹ identity ✓; N = 0 ✓; M flat ⟹ injective by the
      OTHER mathlib lemma regardless — consistent.
    - [3] Hypothesis: only `Flat (Q/N)`; no flatness of Q or N needed for THIS leaf
      (Tor₁(Q/N, M) = 0 suffices) — deliberately weaker than [Mum]'s "all terms flat".
    - [4] Source-drift: [Mum] states more (full SES exactness); the leaf is the
      left-exact clause; the right-exact clause is unconditional. No drift, split is
      finer than source.
    - [5] Discharge: n/a (ours). Composition plan verified against mathlib toolkit:
      `Module.Flat.iff_rTensor_injective` (ideal criterion) NOT needed here; the free
      presentation + `rTensor_exact` chase stays within RightExactness.lean's API.
    - Verdict: SURVIVED.
  - Prior-B2: no match.

- **A3b** (leaf, ours-from-A3): `Module.Flat.of_flat_quotient` — N ⊆ Q, Q flat,
  `Q ⧸ N` flat ⟹ N flat.
  - Source: [Mum] p. 49 Lemma 2 proof (same passage: "all the modules Z^p … are flat
    too" — Mumford's Z^p are exactly kernels of maps of flats with flat image-quotients;
    this leaf is his "easy to see" made precise). Standard: Tor₂(Q/N,·) = 0 shift.
  - Lean ↔ source match: N = Z^p, Q = L^p, Q/N = Z^{p+1} in his notation.
  - Discharge: ours; Tor-free route: `Module.Flat.iff_rTensor_injective'` (ideal
    criterion, verified shape in Flat/Basic at proof time): for f.g. ideal I,
    `I ⊗ N → N` injective ⟵ chase: `I ⊗ N → I ⊗ Q` injective by **A3** (flat quotient
    Q/N), `I ⊗ Q → Q` injective (Q flat), commutativity + N ↪ Q. ~25 LOC.
  - Attacks attempted:
    - [1] Counterexample dropping Q flat: Q = ℤ/4, N = 2ℤ/4, Q/N = ℤ/2 not flat —
      bad example; take Q/N flat forces … over ℤ flat = torsion-free: N = ℤ/2 ⊆ Q =
      ℤ/2 ⊕ ℚ with Q/N = ℚ flat, Q not flat, N = ℤ/2 not flat ✓ Q-flatness needed.
    - [2] Edge: N = 0, N = Q ✓ trivial.
    - [3] Hypothesis: both flatnesses used (attack [1] for Q; for Q/N: N = 2ℤ ⊆ ℤ,
      Q/N = ℤ/2, N ≅ ℤ IS flat — hypothesis not necessary in general?! Check: the
      LEMMA asserts sufficiency, not necessity; fine. No hidden assumptions.)
    - [4] Source-drift: n/a (mechanism leaf).
    - [5] Discharge: chase uses A3 + ideal criterion, 2 cited mathlib names to pin at
      proof time.
    - Verdict: SURVIVED.
  - Prior-B2: no match.

- **A4** (KEY leaf, ours): `kerLTensorComparison_bijective` — with `Q` flat and
  `coker d` flat: the canonical `M ⊗ (ker d) → ker (d.lTensor M)` is bijective (with
  the def-leaf **A0** `kerLTensorComparison` constructing the map unconditionally).
  - Source: GME p. 82, verbatim: *"If n = 1, T₁(𝓕) = T₁(O_S) ⊗_{O_S} 𝓕, and hence T₁
    is an exact functor if R¹f_*𝓛 = T₁(O_S) is locally-free. In this case, T₀ is also
    exact."* + Lemma 1.10.4 (ii) at i = 0 (ι an isomorphism for all quasi-coherent 𝓕).
    Proof source: [Mum] §5 mechanism (Lemma 2 + Cor 2's splitting), in the sharpened
    flat-quotient form of steps 3–4 of the prose proof above.
  - Lean ↔ source: "T₀ exact" for the length-1 complex says M ↦ ker(d ⊗ M) is exact,
    equivalently (Hida's own (i)⟺(ii), p. 80 first diagram) the natural transformation
    ι : T₀(O)⊗𝓕 → T₀(𝓕) is an isomorphism — which is precisely this map's bijectivity,
    naturally in M. "T₁(O_S) locally free" ⟹ `coker d` flat: finite locally free =
    finite projective ⟹ flat (mathlib instances).
  - Discharge: composition of A3 (twice, per prose steps 3–4) + A3b +
    `rTensor_exact`/`lTensor_exact` bookkeeping from RightExactness.lean. ~50 LOC.
  - Attacks attempted:
    - [1] Counterexample without flat coker: R = ℤ, d : ℤ –2→ ℤ, coker = ℤ/2 not flat;
      M = ℤ/2: ker d = 0 so LHS 0; ker(d ⊗ ℤ/2) = ker(0 : ℤ/2 → ℤ/2) = ℤ/2 ≠ 0 —
      bijectivity FAILS ✓ hypothesis sharp, this is the classical jumping example
      (= H⁰ jumps on the fibre).
    - [2] Edge: d = 0 (coker = Q flat ✓): both sides M ⊗ P ✓; d surjective: coker 0
      flat, reduces to A3-split situation ✓; M = R: identity ✓.
    - [3] Hypothesis: Q flat — used for `I⊗Q → Q` in A3b's chase and NOT droppable in
      the route; consumers have Q finite projective ✓. P-flatness NOT assumed ✓ (P
      never needs it — check in proof; if the route surfaces a P-flat need, that's a
      route bug to fix against [Mum], not a hypothesis to add: Mumford's K^p are all
      projective anyway, but the module statement should not over-assume — resolve at
      proof time, ticket records both).
    - [4] Source-drift: GME states T₀ exactness as a FUNCTOR property; the leaf's
      naturality-in-M is carried by the canonical map being the comparison (A0), not
      an ad-hoc iso — matches. The "locally free" vs "flat" gap: for the *criterion*
      flat suffices; GME's locally-free is what the geometric side delivers. Weaker
      hypothesis, same conclusion — no drift (strictly more general).
    - [5] Discharge: internal composition of this file's leaves; sizes grounded:
      [Mum] pp. 49–52 spends ~1.5 pages on the general-p splitting machinery; the
      length-1 sharp form is the 4-step prose above.
    - Verdict: SURVIVED.
  - Prior-B2: no match.

- **A5a** (leaf, mathlib): `ker d` is finite over noetherian R (P finite).
  Discharge: `IsNoetherian.noetherian` / submodule-of-finite; trivial.
  Attacks: [1] no-noeth counterexample exists (kernels of maps of finite free over
  non-noeth non-coherent rings can be non-f.g. — recorded, hypothesis needed);
  [2] edges trivial; [5] mathlib names at proof time. SURVIVED. Prior-B2: none.
- **A5b** (leaf, ours-from-mathlib): `Module.Projective R (ker d)` under noetherian +
  P,Q finite projective + `coker d` flat.
  - Source: Cor 1.10.5 verbatim (quoted in the route section above); [Mum] p. 49:
    *"Note that K⁰ is A-projective, since it is A-flat and finitely generated over a
    noetherian A."*
  - Lean ↔ source: "f_*𝓛 locally O_S-free" = ker d finite projective (= locally free;
    the sheaf-level "locally free" IS finite-projective on affines — this is the
    standard dictionary, and the module form is the affine-local content).
  - Discharge: `im d` finite (A5a route) + flat (A3b) + `Module.FinitePresentation`
    (noeth+finite) ⟹ `Module.Flat.projective_of_finitePresentation` (verified in pin,
    EquationalCriterion.lean:288) ⟹ split `0 → ker d → P → im d → 0` (projective
    lifting) ⟹ ker d a direct summand of finite projective P.
  - Attacks: [1] drop noeth: flat+finite ⇏ projective over general rings? (finite flat
    non-fp exists over non-coherent rings) — noeth load-bearing ✓; [2] edges: d = 0 ⟹
    ker = P ✓; [3] hypotheses minimal modulo the P-flat question of A4[3];
    [4] source states over noetherian ✓ aligned; [5] all three mathlib names verified
    present this session (grep hits recorded above). SURVIVED. Prior-B2: none.

- **A6** (leaf, ours, bookkeeping): `kerBaseChangeEquiv` — for an R-algebra A (flat
  coker, flat Q): `A ⊗[R] ker d ≃ₗ[A] ker (d.baseChange A)` — the A-linear upgrade of
  A4 via `AlgebraTensorModule` unification; this is the exact shape of
  "(f_*𝓛) ⊗ k(s) ≅ f_*(𝓛(s))" consumed at (2.15)/(2.17).
  - Source: GME p. 107 (quoted above) / p. 109: *"Since 𝓛 ∈ Pic¹(S) is fiber by fiber
    of degree 1, as already seen (at the end of Subsection 2.2.1), f_*𝓛 is locally free
    and rank_{O_S}(f_*𝓛) = 1."*
  - Discharge: A4 + `LinearMap.baseChange`/`AlgebraTensorModule.congr` plumbing.
  - Attacks: [1] inherits A4's sharpness; [2] A = R identity ✓; A = κ(𝔭) is the
    consumer ✓; [3] A-linearity (not just R-) is the content — attack "is the A-module
    structure on ker(baseChange) the right one": yes, kernel of A-linear map ✓;
    [4] no drift (this IS the source's displayed iso, with k(s) generalized to A);
    [5] composition ≤ 3 mathlib names. SURVIVED. Prior-B2: none.

### API gaps (COH-1)

None within the module core. The geometric instantiation (K• existence via Čech for
`f : E → Spec A`, comparison with `R^i f_*` sheaves on general S) is **out of scope by
design** (owned COH-3 mathlib lane; deferred interface documented in the route
section). No consumer is blocked: the A6/A7 chains are themselves not yet stated.

## Result T-PIC0 (stage P1): invertible O_X-modules

### Plain-English content (GME 2.2.2 pp. 108–109)

Define, for a scheme X, the tensor product of O_X-modules (sheafified presheaf tensor)
and the property "M is invertible" (an open cover on which M is isomorphic to O). The
unit is invertible; tensoring with the unit is trivial; invertibility is stable under
pullback along any morphism of schemes (a trivializing cover pulls back to a
trivializing cover). The group Pic(X) of (2.16)–(2.17) and the fibre degree are staged
behind GAP-1 and T-PIC-DEG0 respectively (tickets, not skeleton).

### Leaves

- **P0** (def leaf): `Scheme.Modules.tensorObj M N := (sheafification …).obj
  (M.val ⊗ N.val)` + `mk`-level functoriality lemmas.
  - Source: GME p. 108 "Pic⁰ is a group functor with the identity O_E under the
    multiplication: 𝓛 · 𝓛' = 𝓛 ⊗ 𝓛'" — the operation being defined.
  - Discharge: `PresheafOfModules.monoidalCategory` (Presheaf/Monoidal.lean:126) +
    `PresheafOfModules.sheafification` adjunction (used at Modules/Sheaf.lean:69) —
    both verified in pin. Risk noted: instance unification of `X.ringCatSheaf.obj`
    with the `R ⋙ forget₂ _ _` instance shape (abbrev-transparency); fallback is
    calling `Monoidal.tensorObj` explicitly.
  - Attacks: [1] n/a (def); [2] edge M = unit handled by P1c; [3] design attack —
    "should the def sheafify?": presheaf tensor of sheaves is not a sheaf in general
    (standard), sheafification is forced for a value in X.Modules ✓; [4] source
    defines ⊗ of invertible sheaves — classical scheme ⊗; sheafified-presheaf-⊗ is the
    standard construction of it ✓; [5] both mathlib ingredients verified present.
    SURVIVED. Prior-B2: none.
- **P1a** (leaf): `isInvertible_unit : IsInvertible (unit)` — witness cover {⊤},
  identity iso. Discharge: `Modules.pullback (⊤).ι ≅ id`-style + unit-pullback iso
  (PullbackFree.lean `pullbackObjUnitToUnit` — for the finality hypothesis see P1d
  attack log). Attacks: [2] X empty: cover ∅? — use ι = PUnit, U = ⊤ (⊤ = ⊥ on empty X,
  still a cover ✓); [3] def-level attack: `IsInvertible` via covers vs. stalks vs.
  IsLocallyFree-rank-1 — cover form chosen (matches "the formation of an invertible
  sheaf is local", (2.17)); comparison lemma to `SheafOfModules.IsLocallyFree` recorded
  as follow-up, not a leaf. SURVIVED. Prior-B2: none.
- **P1c** (leaf): `tensorObjUnitIso : tensorObj M (unit) ≅ M` (and symm) — presheaf
  right-unitor + "sheafification of a sheaf is itself" (adjunction counit iso on
  sheaves). No GAP-1 content (no double sheafification). Attacks: [1]–[5] routine;
  the only risk is which side (left/right unitor) — both stated? NO: one leaf, one
  conclusion; the symmetric one via the braiding later. SURVIVED. Prior-B2: none.
- **P1b** (leaf, GAP-1-GATED): `IsInvertible.tensorObj` — tensor of invertibles is
  invertible. Route: common refinement cover; on each piece both factors trivial;
  `tensorObj (unit) (unit) ≅ unit` (P1c); the restriction-commutes-with-tensorObj step
  is GAP-1. Skeleton carries the statement + sorry; ticket blocked on GAP-1 scoping.
  Attacks: [1] no counterexample (classical fact); [3] the gap is honestly surfaced,
  not smuggled; [4] source: "the group of isomorphism classes of all invertible
  sheaves" presumes closure under ⊗ — classical ✓. SURVIVED as statement; proof gated.
- **P1d** (leaf): `IsInvertible.pullback` — `(pullback f).obj M` invertible for
  invertible M. Route: preimage cover (`iSup (f ⁻¹ᵁ U i) = ⊤` from `iSup U = ⊤`,
  continuity), `pullbackComp` isos to reduce to the trivializing piece, unit-pullback
  iso. GAP-1-free (no tensor). Attacks: [1] classical, no counterexample; [2] f = 𝟙 ✓
  identity cover; [5] discharge chain: `Scheme.Opens.ι`, `morphismRestrict_ι`,
  `Modules.pullbackComp` (verified in file), `pullbackObjUnitToUnit` — ATTACK: the
  mathlib iso needs the site functor final; for `Opens.map f.base` finality holds by
  the lattice-meet zig-zag (comma categories nonempty via ⊤, connected via ⊓) — to
  re-verify against mathlib's `Functor.Final` at proof time; if mathlib lacks the
  instance it is a 15-line lemma. SURVIVED with a named proof-time check. Prior-B2:
  none.

### API gaps (T-PIC0)

- **GAP-1** (described in the route section): sheafification ⊗-compatibility /
  restriction-commutes-with-sheafification on the Zariski site. Blocks P1b and all of
  stage P2 (the Pic group + (2.16)/(2.17)). Own `/develop` pass required; ecosystem
  check (Riou lane) FIRST. Not silently absorbed anywhere: the only skeleton sorry it
  gates is P1b.
- **T-PIC-DEG0** (scoping, no skeleton): fibre degree — audit the HasseWeil
  divisor/degree anchor (ecosystem survey §3 confirms ClassGroup/Pic⁰ machinery exists
  there) and cut statements. Consumer: Pic^ν, (2.16).

## Confidence gate (Step 5) — status

1. Every leaf discharged-or-gap: ✓ (A1–A6 mathlib/ours-with-plan; P0–P1d mathlib/ours;
   P1b explicitly GAP-1-gated; gaps have sub-development plans).
2. Skeleton compiles: ✓ — `lake build ModularCurves.ForMathlib.BaseChangeKerCoker`
   green (8 sorry warnings, 0 errors) and `lake build ModularCurves.Picard.
   InvertibleSheaf` green (4 sorry warnings, 0 errors), 2026-07-08T11:55Z; both
   registered in the root module. All `def`s (A0 `kerLTensorComparison`, A6-side
   `kerBaseChangeComparison`, P0 `tensorObj`/`unitObj`, `IsInvertible`) are fully
   implemented — zero data-sorries (standing rule 2). Notes from elaboration: the
   presheaf monoidal instance needed an `inferInstanceAs` bridge through
   `X.ringCatSheaf.obj = X.sheaf.obj ⋙ forget₂ CommRingCat RingCat` (recorded in-file);
   A1 is stated as the range equality `range (f.lTensor M) = range ((range f).subtype.
   lTensor M)` — the consumer equiv is then mathlib's `tensorQuotientEquiv` composed
   with `Submodule.quotEquivOfEq`, so no bespoke equiv def is needed.
3. Verbatim quote per leaf: ✓ (above; internal nodes cite composition).
4. Adversarial pass per leaf: ✓ (blocks above; A2's attack [1] hardened a hypothesis —
   ℚ/ℤ counterexample recorded in the docstring).
5. Prior-B2 consulted: ✓ this session — `b2_log.jsonl` has 1 real B2 (T-A4,
   `isWeierstrassModel_unique`, Weierstrass-model uniqueness) + 1 event line; no name
   or shape overlap with any leaf here.
6. Tree mirrors source: ✓ — [Mum] §5's own chain (Čech ⟶ Lemma 1 ⟶ Lemma 2 ⟶
   Corollaries) is mirrored with the Čech/Lemma-1 half explicitly deferred (interface)
   and the criterion half as A-leaves; GME's statements are the consumer-facing forms
   (mapping table in the route section). LOC estimates grounded in source line counts
   (recorded per leaf).
7. Single-conclusion leaves: ✓ (Cor 1.10.5's two sentences = A5b vs. a
   consumer-assembly later; Lemma 1.10.4's (i)⟺(ii) split into A1/A4 directions;
   nothing bundles an ∧).

## Feasibility assessment

The COH-1 module core is fully dischargeable against the current pin: the two
genuinely new pieces (A3 purity, A3b flat-two-out-of-three) are classical sub-page
lemmas with Tor-free routes inside mathlib's existing `RightExactness`/`Flat` API, and
everything else is ≤ 3-lemma composition over verified names. The deliberate cut —
criterion now, Čech instantiation deferred to the owned mathlib lane — matches both
sources' own architecture ([Mum] assumes coherence; Hida cites [ALG] III.12.10) and
blocks no current consumer. T-PIC0 stage P1 lands the tensor + invertibility API with
one honestly-surfaced gap (GAP-1) gating the tensor-closure lemma and the future group;
GAP-1 is the single load-bearing unknown of the stream and gets its own scoping pass
with an upstream-coordination checkpoint before any build.
