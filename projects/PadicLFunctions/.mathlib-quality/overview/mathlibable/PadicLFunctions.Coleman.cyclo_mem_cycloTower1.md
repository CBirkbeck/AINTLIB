# `/mathlibable` report — `PadicLFunctions.Coleman.cyclo_mem_cycloTower1`

**Final verdict: `NO-composable-from-mathlib`**

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per task build note). The
  declaration and its full dependency chain were read directly from
  `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean`,
  `.../Iwasawa/LocalUnits.lean`, `.../Coleman/Map.lean`, and `.../Coleman/Tower.lean`. The file's
  only recent commits are the daily mathlib bump and golf cleanups (no new math), and the sibling
  decls in the same file already have completed `/mathlibable` reports, so the file is in a built,
  sorry-free state.
- decl `PadicLFunctions.Coleman.cyclo_mem_cycloTower1`: resolved at
  `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:472`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Cyclotomic units — the global modules `𝒟_n` and their local closures `𝒞`
  (RJW arXiv:2309.15692 §11.3); culminates in **this** milestone (RJW TeX 3084): the Coleman-map
  inputs `c_n(a)` "are naturally elements of `𝒟_n`, hence global" — `cyclo ∈ 𝒞_{∞,1} ≤ 𝒰_{∞,1}`.

The full text:

```lean
theorem cyclo_mem_cycloTower1 {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (hp2 : p ≠ 2)
    (ha1 : a ≡ 1 [MOD p]) :
    cyclo p ha hp2 ∈ cycloTower1 p := by
  intro n hn
  have hmemD : (cyclo p ha hp2).elems n ∈ cycloUnits p n :=
    cyclo_elems_mem_cycloUnits p ha hp2 hn
  have hmemloc : (cyclo p ha hp2).elems n ∈ localUnits p n :=
    globalUnits_le_localUnits p n (cycloUnits_le_globalUnits p n hmemD)
  have hval : ((cyclo p ha hp2).elems n : ℂ_[p]) = cycloUnit p a n := by
    change ((if hn : 1 ≤ n then Units.mk0 (cycloUnit p a n)
      (cycloUnit_ne_zero p ha hn) else 1 : ℂ_[p]ˣ) : ℂ_[p]) = _
    rw [dif_pos hn, Units.val_mk0]
  rw [cycloClosureOne, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [cycloClosure, Subgroup.mem_inf]
    exact ⟨Subgroup.le_topologicalClosure _ hmemD, hmemloc⟩
  · rw [mem_localUnitsOne_iff]
    refine ⟨hmemloc, ?_⟩
    rw [hval]
    exact norm_cycloUnit_sub_one_lt_one p ha hn ha1
```

---

### Statement (Phase 1)

`cyclo_mem_cycloTower1` is a theorem stating the following:

Fix an odd prime `p` and a natural number `a` with `p ∤ a` and `a ≡ 1 (mod p)`. The packaged
**norm-compatible system of cyclotomic units** `c(a) = (c_n(a))_n` — where `c_n(a) = (ξ^a − 1)/(ξ − 1)`
is the cyclotomic unit of the `p^n`-th cyclotomic local field, ξ a primitive `p^n`-th root of unity —
is an element of the inverse-limit tower `𝒞_{∞,1}`: the projective limit (under the level norm maps
`N_{n+1,n}`) of the **`p`-adic closures of the cyclotomic units intersected with the principal local
units** `𝒞_{n,1} = 𝒞_n ∩ 𝒰_{n,1}`. This is RJW arXiv:2309.15692 TeX 3084 — the assertion that the
Coleman-map inputs `c_n(a)` "are naturally elements of `𝒟_n`, hence global", lifted to the closed-up
principal-unit tower that is the actual domain of the Coleman map (`coleman_to_kl`).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the fixed prime (section variables).
- `a : ℕ` — the index of the cyclotomic unit `c_n(a)` (an implicit argument).

Hypotheses (Lean side):
- `ha : ¬ (p : ℕ) ∣ a` — `p ∤ a`, so `c_n(a)` is a genuine unit (norm 1) and `cyclo` is well-defined.
- `hp2 : p ≠ 2` — `p` is odd (needed for the level-norm compatibility `levelNorm_cycloUnit` packaging
  `cyclo`, and downstream).
- `ha1 : a ≡ 1 [MOD p]` — the congruence that makes `c_n(a)` a *principal* unit
  (`‖c_n(a) − 1‖ < 1`). **Statement note (T1113)**: this hypothesis was added by the project because
  for `a ≢ 1 (mod p)`, `c_n(a) ≡ a (mod 𝔭_n)` is not principal, so membership in
  `𝒞_{n,1} = 𝒞_n ∩ 𝒰_{n,1}` genuinely requires it; RJW glosses this (the §12 arguments use the
  principal-unit part).

Conclusion (math): the cyclotomic-unit norm-compatible system lies in the cyclotomic-closure principal
tower `𝒞_{∞,1}` inside `𝒰_∞`.

Conclusion (Lean): `cyclo p ha hp2 ∈ cycloTower1 p`, i.e. (unfolding the carrier predicate of
`cycloTower1`) `∀ n, 1 ≤ n → (cyclo p ha hp2).elems n ∈ cycloClosureOne p n`, where
`cycloClosureOne p n = ((cycloUnits p n).topologicalClosure ⊓ localUnits p n) ⊓ localUnitsOne p n`.

Key definitional facts (all project-local; `Iwasawa/CyclotomicUnits.lean`, `Iwasawa/LocalUnits.lean`,
`Coleman/Map.lean`, `Coleman/Tower.lean`):
- `cyclo p ha hp2`        : `NormCompatUnits p` — the system `(c_n(a))_n`, level 0 set to `1`   (Map.lean:180)
- `cycloTower1 p`         := `{u | ∀ n, 1 ≤ n → u.elems n ∈ cycloClosureOne p n}`               (CyclotomicUnits.lean:226)
- `cycloClosureOne p n`   := `cycloClosure p n ⊓ localUnitsOne p n`                              (CyclotomicUnits.lean:218)
- `cycloClosure p n`      := `(cycloUnits p n).topologicalClosure ⊓ localUnits p n`              (CyclotomicUnits.lean:210)
- `cycloUnits p n`        := `Subgroup.closure (cycloGenSet p n) ⊓ globalUnits p n`              (CyclotomicUnits.lean:182)
- `localUnitsOne p n`     := principal units `{u ∈ 𝒰_n : ‖u − 1‖ < 1}`                           (LocalUnits.lean:71)
- `NormCompatUnits p`     : `structure` (norm-inverse-limit of local unit groups)               (Tower.lean:650)

So the conclusion is a level-wise membership in a **triple meet** of project-bespoke subgroups, and the
proof discharges each factor from a previously-proved lemma.

---

### Size classification (Phase 2a)

Verdict: **BIG** (by the skill's own criteria) — it is explicitly the file's `## Main results`
**milestone** (RJW TeX 3084, called out verbatim in the module docstring and the decl's own docstring as
"**MILESTONE**"). It is the headline mathematical statement the whole file builds toward.

Reason: named-as-milestone main result of the development; the genuine content of §11.3.

Caveat that drives the verdict: "BIG" here means *mathematically central to the project*, **not**
"big for mathlib". The statement is `cyclo p ha hp2 ∈ cycloTower1 p` — a membership assertion whose
subject (`cyclo`) and target (`cycloTower1`) are **both** objects that exist only in this project and
have **no** mathlib counterpart (Phase 5: 0 mathlib hits for `cyclo`/`cycloTower1`/`cycloClosureOne`/
`cycloClosure`/`cycloUnits`/`localUnitsOne`/`NormCompatUnits`). A project-central milestone about
project-bespoke objects is not, by that fact, a mathlib candidate.

(Note: literature width was run EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~18 substantive lines (a `by` tactic proof, not a one-liner).
One-liner verdict: **n/a — kind is `theorem`, not `def`** (the defeq/diamond/API exemption table is for
`def`/`abbrev`/`structure`; a theorem introduces no definitional equality or typeclass-search path).

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

The theorem has two separable concepts: (i) the **number-theoretic content** — the norm-compatible
system of cyclotomic units lies in the cyclotomic tower `𝒞_{∞,1}` of principal-local-unit closures
(classical Iwasawa theory; the RJW paper is the immediate, and in WebSearch directly-surfaced, source);
and (ii) the **structural mechanism** actually being executed — membership in a `topologicalClosure`
(`g ∈ G ⊆ closure G`) and in a finite **meet** of subgroups (`x ∈ a ⊓ b ↔ x ∈ a ∧ x ∈ b`), lifted
level-wise through an inverse-limit-of-subgroups predicate. Both were searched.

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific NT form)     | "cyclotomic units norm-compatible system principal local units Iwasawa theory C_infinity cyclotomic tower membership" | yes  | `C_∞ ⊆ U_∞`; cyclotomic/circular units assemble into a norm-compatible tower inside the (principal) local units; projective limits under norm maps form f.g. `ℤ_p[[Γ]]`-modules | Sharifi *Iwasawa theory* notes; Hida *Elementary Iwasawa Theory*; Coates–Sujatha *Cyclotomic Fields and Zeta Values*; Rubin/Euler-systems (arXiv:0910.1411); textbook Iwasawa theory |
|  2 | WebSearch (Coleman-map / aliases)| "cyclotomic units lie in projective limit principal units U_1 Coleman map Iwasawa module circular units" | yes  | `U` = proj. lim. of (semi-)local units, `C` = proj. lim. of cyclotomic units; Coleman power series compute `U/C`; "generators of the modules of cyclotomic units … and their images under the Coleman map are computed" | **RJW arXiv:2309.15692** surfaced directly ("An introduction to p-adic L-functions"); also Coleman *Power Series for K2* (Documenta Math.), Belliard *Global Units mod Circular Units*, JTNB *Semi-local units mod cyclotomic units* |
|  3 | WebSearch (general construction) | "Coates Sujatha cyclotomic fields C_infinity subset U_infinity local units cyclotomic units inverse limit norm maps definition" | yes  | cyclotomic units are products of `(ζ_n^a − 1)`, a finite-index subgroup of the full units; in the tower they "fit together into a norm-compatible tower/system"; inverse limits under norm maps are the standard construction | Wikipedia "Cyclotomic unit"; Coates–Sujatha; Encyclopedia of Mathematics "Cyclotomic field"; Hida |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of 'norm-compatible cyclotomic units ⊆ principal-local-unit cyclotomic tower' and of 'membership in a meet of subgroups / in a topological closure'") | n/a  | —                                | ChatGPT MCP server not configured in this environment (`ToolSearch` for `mcp__chatgpt__*` returns no tool). Recorded n/a; compensated by extra WebSearch breadth (rows 1–3), nLab (row 6), Loogle (Phase 5 B) and direct mathlib source reading (Phase 5 D). |
|  5 | Local references                 | check `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`               | n/a  | (no references dir)              | Neither `.mathlib-quality/references/` nor a gitignored `refs/` store exists for this project (confirmed by `ls`); the RJW arXiv:2309.15692 PDF is not available locally. Recorded n/a — but the source is RJW arXiv:2309.15692, which was surfaced *directly* in WebSearch row 2 and is read about there. |
|  6 | nLab                             | "Iwasawa theory" (cyclotomic units / circular units / `U_∞` / `C_∞` / unit tower)                      | yes (page exists; concept absent) | nLab "Iwasawa theory" centres on the class-group inverse limit `X_∞` and the Main Conjecture; it does **not** discuss cyclotomic units, the local-unit tower `U_∞`, `C_∞`, or any "cyclotomic units ⊆ principal local units" lemma | WebFetch of `ncatlab.org/nlab/show/Iwasawa+theory`: confirms there is **no named lemma** for this inclusion; it is ambient definitional background, not a quotable result |
|  7 | nCatLab (if categorical)         | (covered by nLab row 6)                                                                                 | n/a  | not a higher-categorical concept | The statement is a concrete membership in `p`-adic unit groups; no ∞-categorical content. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | not an algebraic-geometry concept | `p`-adic / Iwasawa number theory; Stacks has no bearing. (The only adjacent general fact — "the integral closure is a ring", Stacks 00GO — feeds the *dependency* `isIntegral_cycloUnit`, not this milestone.) |
|  9 | MathOverflow / Math.StackExchange| "cyclotomic units principal units inverse limit" / "membership in meet of subgroups topological closure" | yes  | confirms the NT inclusion is standard ambient background (never a quotable named lemma); confirms `x ∈ a ⊓ b ↔ x∈a ∧ x∈b` and `G ⊆ closure G` are elementary | The structural facts are "too elementary to have project-independent names"; the NT inclusion is background in every Iwasawa text |
| 10 | recent arXiv (last 5 years)      | RJW arXiv:2309.15692 (the project's own source); also arXiv:0910.1411 (Euler systems), math/0512015 (Iwasawa), JTNB:1284 (semi-local units mod cyclotomic units) | yes  | RJW §11.3 (TeX 3060–3112): defines `𝒞_{∞,1} = lim←_{n≥1} 𝒞_{n,1}`, `𝒞_{n,1} = 𝒞_n ∩ 𝒰_{n,1}`; TeX 3084 asserts `c_n(a) ∈ 𝒟_n` "hence global"; the membership in the closed-up principal tower is the milestone, used as the Coleman-map input | The source states this milestone in exactly the form the Lean theorem proves; the principal-unit subtlety (`a ≡ 1 mod p`) is glossed in RJW and made explicit by the project (T1113 note) |

The protocol passes: WebSearch ran 3 distinct queries at different generality levels (specific NT form,
the Coleman-map/aliases form, the general inverse-limit-construction form) and surfaced the project's own
source RJW arXiv:2309.15692; ChatGPT MCP recorded n/a with reason (not installed); local references
recorded n/a with reason; nLab checked (page exists, concept/lemma absent); nCatLab / Stacks /
MathOverflow / arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **the milestone inclusion of the cyclotomic-unit norm-compatible system into the
cyclotomic tower of principal-local-unit closures** — `(c_n(a))_n ∈ 𝒞_{∞,1}` (classical Iwasawa theory;
RJW arXiv:2309.15692 §11.3 TeX 3084 is the immediate source). Its proof packages two standard ingredients:
(NT) "cyclotomic units are global units / sit inside the local units of the cyclotomic tower" and
(structure) "membership in a meet of subgroups and in a topological closure", lifted level-wise.

Sources agree on the standard form: **yes**. The NT statement (cyclotomic units assemble into a
norm-compatible tower inside the local units; `C_∞ ⊆ U_∞`) is uniform across Washington, Lang, Coates–
Sujatha, Hida, Sharifi, Coleman, Belliard, and RJW. It is treated everywhere as **definitional/ambient
background**, never as a separately-named quotable theorem (confirmed by nLab having no such lemma).

Most general standard form: the *structural* skeleton is `Subgroup.mem_inf`
(`x ∈ a ⊓ b ↔ x ∈ a ∧ x ∈ b`, equivalently `inf_le_right`/`inf_le_left`) together with
`Subgroup.le_topologicalClosure` (`G ≤ closure G`) — both maximally general in mathlib. Everything else
(`cyclo`, `cycloTower1`, `cycloClosureOne`, `cycloClosure`, `cycloUnits`, `localUnits`, `localUnitsOne`,
`NormCompatUnits`) is bespoke RJW-tower scaffolding with no literature-standard or mathlib counterpart.

Generality dimensions where the literature varies:
  - The NT objects (`𝒞`, `𝒰` towers): RJW realises them concretely inside `ℂ_p`; Washington/Lang/Coates–
    Sujatha use abstract local/global cyclotomic fields. Either way they are **not** mathlib objects.
  - The genuine algebraic facts (`c_n(a)` is integral with integral inverse, `‖c_n(a) − 1‖ < 1` when
    `a ≡ 1 mod p`) are proved in *separate* dependency lemmas (`cyclo_elems_mem_cycloUnits`,
    `isIntegral_cycloUnit`, `norm_cycloUnit_sub_one_lt_one`), each of which has its own `/mathlibable`
    report; this milestone only *assembles* them.
  - The structural facts (`mem_inf`, `le_topologicalClosure`) are already maximally general in mathlib.

Disagreement with the literature: **none**. The Lean statement matches RJW's milestone; the added
`a ≡ 1 (mod p)` hypothesis (T1113) is a *correctness* tightening (the literature's gloss), not a deviation.

---

### Generality analysis — `cyclo_mem_cycloTower1` (Phase 4)

Literature-standard form (from Phase 3): semantically the RJW milestone `(c_n(a))_n ∈ 𝒞_{∞,1}`;
structurally the assembly of `Subgroup.mem_inf` + `Subgroup.le_topologicalClosure` over project objects,
fed by the three content lemmas.

| # | Parameter / hypothesis            | Current Lean form                         | Literature-standard form                 | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|-------------------------------------------|------------------------------------------|---------------------|----------------------------------|
| 1 | `cyclo p ha hp2` (the subject)    | bespoke `NormCompatUnits p` system `(c_n(a))_n` | the norm-compatible cyclotomic-unit system (classical) — but no mathlib object | NO | `cyclo`, `NormCompatUnits`, `cycloUnit` are project-only (Phase 5: 0 mathlib hits). The statement is intrinsically about this object. |
| 2 | `cycloTower1 p` (the target)      | bespoke inverse-limit subgroup of `NormCompatUnits p` | `𝒞_{∞,1}` (classical) — but no mathlib object | NO | Glued from project-only defs (`cycloClosureOne`/`cycloClosure`/`cycloUnits`/`localUnits`/`localUnitsOne`), none in mathlib. |
| 3 | `ha : ¬ p ∣ a`                    | `p ∤ a`                                   | coprimality `gcd(a, p^n) = 1` (standard for cyclotomic units to be units) | marginal/NO | Needed for `c_n(a)` to be a unit (norm 1); equals the standard coprimality hypothesis. Not a generalisation axis — relaxing it makes `c_n(a)` a non-unit. |
| 4 | `hp2 : p ≠ 2`                     | `p` odd                                   | RJW imposes odd `p` throughout §11–12 | NO | Required by the level-norm packaging (`levelNorm_cycloUnit`) and the principal-unit estimate; it is the source's standing hypothesis, not a removable specialisation. |
| 5 | `ha1 : a ≡ 1 [MOD p]`             | principal-unit congruence                 | the literature's (often glossed) principal-unit condition | NO | This is a *correctness* hypothesis (T1113): without it the conclusion is false (`c_n(a)` not principal ⇒ not in `𝒰_{n,1}`). Cannot be weakened. |
| 6 | the structural kernel             | `Subgroup.mem_inf` / `Subgroup.le_topologicalClosure` threaded level-wise | the same, maximally general in mathlib | (already maximal) | The abstract content is already mathlib's most general meet-projection + closure-containment; no further generalisation of the *facts* is meaningful. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the objects it is about). Zero weakening opportunities:
every hypothesis (`ha`, `hp2`, `ha1`) is either the standard coprimality/odd-prime hypothesis of the
theory or a strict correctness requirement (the T1113 principal-unit congruence), and the only abstract
content (`mem_inf`, `le_topologicalClosure`) is already at mathlib's maximal generality. The statement
cannot be weakened without either (a) becoming a statement about different (non-existent-in-mathlib)
objects, or (b) becoming false (dropping `ha1`).

Number of weakening opportunities found: 0
Proposed restatement: none (MAXIMALLY GENERAL).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                      | no       | —                      | Hypotheses are the `p`/`Fact p.Prime` section vars plus the arithmetic conditions on `a`; nothing to typeclass-ify. |
|  2 | sequences/metric → filters/topological?                                                                  | no       | —                      | The tower is indexed over `ℕ` with an `n ≥ 1` predicate (the inverse-system index, not a metric limit); and the *one* topological step already uses mathlib's `topologicalClosure`, the idiomatic tool. Already filter/topology-correct. |
|  3 | construct an object → universal-property class?                                                          | no       | —                      | This is a membership theorem, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure?                                                       | no       | —                      | All objects are already bundled `Subgroup`s; the proof uses `Subgroup.mem_inf` / `Subgroup.le_topologicalClosure`. Idiomatic. |
|  5 | vector-space/metric/field-specific → weaker typeclass?                                                   | no       | —                      | No algebraic-structure hypothesis to weaken; the abstract core already lives over `SemilatticeInf` (meet) and a topological group (closure). |
|  6 | 1-categorical → higher-categorical?                                                                      | no       | —                      | Concrete unit-group membership; no categorification target. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure?                                          | no       | —                      | The `ℕ`-index is the inverse-system's directed index; abstracting it means re-engineering `NormCompatUnits`, the project's chosen model, not a mathlib idiom gap. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: the theorem is already stated and proved idiomatically (bundled `Subgroup`s,
`Subgroup.mem_inf`, `Subgroup.le_topologicalClosure`, section typeclasses); its abstract kernels are
already mathlib's maximally-general primitives. There is no Bourbaki-2.0 reformulation to make — the
subject and target are project-bespoke and out of mathlib scope.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equality or typeclass-search path is introduced).

---

### Mathlib search-status: `cyclo_mem_cycloTower1` (Phase 5)

Note on environment: the Lean MCP search tools (`lean_loogle`, `lean_leansearch`, `lean_local_search`,
Lean-Finder) are not installed here (`ToolSearch` for `mcp__lean__*` returns no tool); Loogle was run via
its public JSON endpoint (WebFetch), and method D (grep mathlib source) was run directly. Each method is
recorded with what was actually executed.

[A] Lean-Finder       "cyclotomic units in principal local unit tower", "membership in meet of subgroups and topological closure"  —  n/a: MCP/web app not reachable from this harness; subsumed by Loogle (B), grep (D), and the Phase-3 literature sweep, which jointly resolve the question.
[B] Loogle            `?a ⊓ ?b ≤ ?b` (the structural kernel)  →  hits: `inf_le_right` (`Mathlib.Order.Lattice`, `SemilatticeInf`), `min_le_right`, etc. (verified via the public JSON endpoint). Also the relevant `Subgroup.mem_inf` and `Subgroup.le_topologicalClosure` are confirmed by grep (D). Loogle on the *concrete* statement (`cyclo _ ∈ cycloTower1 _`) is impossible — the constants are project-local, indexed in no Loogle library.
[C] LeanSearch        "norm-compatible cyclotomic units lie in the principal local unit tower" / "element of subgroup is in its topological closure and in a meet"  —  n/a: NL endpoint not reachable from this harness; the abstract content (`mem_inf`, `le_topologicalClosure`) is unambiguous and already pinned by Loogle/grep, so NL search adds nothing.
[D] Grep mathlib src  `NormCompatUnits`, `cyclo`, `cycloTower1`, `cycloClosureOne`, `cycloClosure`, `cycloUnits`, `localUnits`, `localUnitsOne` over `.lake/packages/mathlib/Mathlib/`  →  **0 hits each** (all eight are project-only). Searched the existing mathlib cyclotomic-units file `Mathlib/RingTheory/RootsOfUnity/CyclotomicUnits.lean`: it contains only **per-element associatedness** facts (`associated_sub_one_pow_sub_one_of_coprime`, `associated_pow_sub_one_pow_of_coprime`, `geom_sum_isUnit`, `pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one`, …) — **no** group/subgroup of cyclotomic units, **no** local closures, **no** inverse-limit tower, **no** membership-in-tower result. The building blocks `Subgroup.mem_inf` (`Mathlib/Algebra/Group/Subgroup/Lattice.lean`) and `Subgroup.le_topologicalClosure` (`Mathlib/Topology/Algebra/Group/…`) **are** in mathlib.
[E] Name pattern      grep project + mathlib for `*_mem_cyclo*`, `*mem_*Tower*`, `*mem_topologicalClosure*`, `le_topologicalClosure`  →  in mathlib: `Subgroup.le_topologicalClosure`, `Subgroup.mem_inf`. In the project: an entire bespoke family of *analogous* membership lemmas about *other* tower elements (`wGamma_mem_cycloTower1`, `wGamma_pow_mem_cycloTower1`, `galNCU_wGamma_mem_cycloTower1`, `galNCU_neg_one_mem_cycloTower1`, `zpPow_zetaSys_mem_cycloClosureOne`, `mem_cycloClosureOne_of_pow_mem` — all in `IwasawaProof/Generators.lean`). None of these is a mathlib name, and none subsumes the concrete statement.

Searched for both:
  - the user's current form (`cyclo p ha hp2 ∈ cycloTower1 p`) — built entirely from project-only
    constants; **not in mathlib** (cannot be, by construction).
  - the literature-standard / abstract forms — `Subgroup.mem_inf` and `Subgroup.le_topologicalClosure`
    **are** in mathlib (the meet-projection and closure-containment primitives the proof is a level-wise
    wrapper of); mathlib's only cyclotomic-unit content is per-element associatedness, **not** the
    subgroup/closure/tower objects this theorem is about.

Concluded: **found building blocks (`Subgroup.mem_inf`, `Subgroup.le_topologicalClosure`, plus the three
project content-lemmas); composition would yield our form.** The exact concrete statement is **not** in
mathlib (it is about objects that exist only in this project, and depends on three project-specific
content lemmas that are themselves not in mathlib), but its remaining proof content — *given those
lemmas* — is a short chain of mathlib's meet-projection and closure-containment primitives threaded
through the project's pointwise tower definition.

---

### Call sites — `cyclo_mem_cycloTower1` (Phase 6.0)

Internal use count: **1** (within the project, NOT counting the declaring line 472).
External-to-file callers: **0** distinct files (the single use is *inside* the declaring file).
External-to-project callers: **0** (no downstream library consumes it).

| Caller file:line                                   | Usage pattern (one-line excerpt)                                                            |
|----------------------------------------------------|--------------------------------------------------------------------------------------------|
| Iwasawa/CyclotomicUnits.lean:498                   | `cycloTower1_le_unitsTower1 p (cyclo_mem_cycloTower1 p ha hp2 ha1)` (proves the sibling milestone `cyclo_mem_unitsTower1`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the theorem?):
  - The *analogous* milestone membership results in `IwasawaProof/Generators.lean`
    (`wGamma_mem_cycloTower1`, `galNCU_wGamma_mem_cycloTower1`, …) prove membership in `cycloTower1` for
    **different** elements (`wGamma`, `galNCU`), routing through `mem_cycloClosureOne_of_pow_mem` and
    `zpPow_zetaSys_mem_cycloClosureOne` — they are **not** re-derivations of *this* theorem's `cyclo`
    statement, so they do not count as inline duplicates of it.
  - For the specific element `cyclo p ha hp2`, the membership is established **only** here; its one
    downstream consumer (`cyclo_mem_unitsTower1`) calls it directly.

Per the Phase-6 signal table, **K = 1 internal use only** is the "possibly the wrong abstraction — could
be inlined; lean toward NO-composable" pattern. Here the single consumer is the trivially-related sibling
`cyclo_mem_unitsTower1 := cycloTower1_le_unitsTower1 p (cyclo_mem_cycloTower1 …)`. But the decisive factor
is independent of usage count: the *objects* are out of mathlib scope (Phase 5: 0 mathlib hits for `cyclo`
/ `cycloTower1` / `cycloClosureOne` / `cycloUnits` / `localUnitsOne` / `NormCompatUnits`), which caps the
verdict at a NO bucket regardless.

### Composition check (Phase 6)

Can `cyclo_mem_cycloTower1` be derived from mathlib in ≤3 chained calls? (Here "from mathlib" means:
*given the project's own definitions and the project's own content lemmas it cites*, is the residual proof
a trivial composition of mathlib primitives, so that no standalone *mathlib-worthy* lemma is created?)

Attempt 1: the existing proof, read as a composition over the cited lemmas —
```
intro n hn
-- (content, proved elsewhere) hmemD : (cyclo …).elems n ∈ cycloUnits p n   [cyclo_elems_mem_cycloUnits]
-- (content, proved elsewhere) ‖c_n(a) − 1‖ < 1                              [norm_cycloUnit_sub_one_lt_one]
rw [cycloClosureOne, Subgroup.mem_inf]; refine ⟨?_, ?_⟩
· rw [cycloClosure, Subgroup.mem_inf]; exact ⟨Subgroup.le_topologicalClosure _ hmemD, hmemloc⟩
· rw [mem_localUnitsOne_iff]; exact ⟨hmemloc, …⟩
```
  - Mathlib decls used (the residual glue): `Subgroup.mem_inf` (used twice, to split the triple meet
    `(closure ⊓ localUnits) ⊓ localUnitsOne`), `Subgroup.le_topologicalClosure` (`G ≤ closure G`, the
    closure-containment), and the project lemmas `globalUnits_le_localUnits`, `cycloUnits_le_globalUnits`,
    `mem_localUnitsOne_iff`.
  - **Project content-lemmas used (NOT mathlib, NOT a composition)**: `cyclo_elems_mem_cycloUnits` (the
    word `(ξ^a−1)(ξ−1)⁻¹` + global integrality — genuine algebra, RJW TeX 3084) and
    `norm_cycloUnit_sub_one_lt_one` (the ultrametric principal-unit estimate `‖c_n(a) − 1‖ < 1`).
  - Result: **the residual assembly succeeds as a short mathlib-primitive composition** (two
    `Subgroup.mem_inf` splits + one `Subgroup.le_topologicalClosure` + bundling), **but only after the two
    project content-lemmas have done the real work**.
  - Notes: This is the crucial reading. The theorem is **not** composable *from mathlib alone* — its truth
    rests on `cyclo_elems_mem_cycloUnits` and `norm_cycloUnit_sub_one_lt_one`, which are project results
    with their own (non-trivial) proofs and their own `/mathlibable` reports. What it **is**, is a thin
    *assembly layer* that, given those project lemmas, threads them through mathlib's `mem_inf` /
    `le_topologicalClosure` primitives into the project-bespoke `cycloClosureOne`/`cycloTower1` packaging.

Conclusion: **COMPOSABLE — as an assembly over project lemmas + mathlib primitives, into project-bespoke
objects.** It creates **no** new mathlib-worthy content: the genuine mathematics is in the cited
dependency lemmas (each separately assessed), and the residual is `Subgroup.mem_inf` (×2) +
`Subgroup.le_topologicalClosure`, threaded through the project's own definitions. There is nothing here
to upstream as a standalone mathlib lemma.

---

## Verdict: `cyclo_mem_cycloTower1`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the milestone `(c_n(a))_n ∈ 𝒞_{∞,1}` is **classical Iwasawa theory**
  (Coates–Sujatha, Washington, Lang, Hida, Sharifi, Coleman, Belliard), with the project's own source
  RJW arXiv:2309.15692 §11.3 (TeX 3084) surfaced directly in WebSearch. The inclusion is **ambient
  definitional background** — never a separately-named quotable theorem (nLab "Iwasawa theory" has no
  such lemma). The structural kernels are the elementary `Subgroup.mem_inf` and
  `Subgroup.le_topologicalClosure`. Nothing novel for mathlib.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (0 weakenings — all hypotheses are standard
  coprimality/odd-prime conditions or the strict T1113 correctness congruence); modern-idiom: **none** —
  already idiomatic; the abstract kernels are already maximally general in mathlib.
- Mathlib search (Phase 5): the concrete statement is **not in mathlib** — `cyclo`, `cycloTower1`,
  `cycloClosureOne`, `cycloClosure`, `cycloUnits`, `localUnits`, `localUnitsOne`, `NormCompatUnits` all
  have **0 mathlib hits** (project-only); mathlib's `RingTheory/RootsOfUnity/CyclotomicUnits.lean` has
  only per-element *associatedness* facts, not the subgroup/closure/tower objects. The building blocks
  `Subgroup.mem_inf` / `Subgroup.le_topologicalClosure` **are** in mathlib.
- Composition check (Phase 6): **COMPOSABLE** — given the project's two content-lemmas
  (`cyclo_elems_mem_cycloUnits`, `norm_cycloUnit_sub_one_lt_one`), the residual is two `Subgroup.mem_inf`
  splits + one `Subgroup.le_topologicalClosure` + bundling, threaded into project-bespoke objects. No new
  mathlib-worthy content.

**Rationale:**

This is the project's headline milestone (RJW TeX 3084), and *mathematically* it is genuine and central:
the norm-compatible system of cyclotomic units `(c_n(a))_n` lands in the closed-up principal-unit tower
`𝒞_{∞,1}` — the Coleman map's input. But for the **mathlib question** it is not a candidate in any form,
for two independent reasons. First, its **subject and target are objects mathlib does not have and will
not have**: `cyclo` / `NormCompatUnits` (the norm-inverse-limit unit system realised inside `ℂ_p`),
`cycloTower1` / `cycloClosureOne` / `cycloClosure` / `cycloUnits` (RJW's concrete cyclotomic-closure
towers), and `localUnits` / `localUnitsOne` are all bespoke RJW scaffolding — Phase 5 returns zero mathlib
hits for every one, and mathlib's own cyclotomic-units file deliberately stops at per-element
associatedness. A theorem whose statement is `cyclo ∈ cycloTower1` cannot be stated in mathlib without
first importing all of that bespoke infrastructure, which is exactly the project-specific Iwasawa-theory
development that AINTLIB exists to build, not mathlib.

Second, **the genuine mathematics is not in this declaration** — it is in the lemmas this milestone
*assembles*. The two pieces of real content are (i) `cyclo_elems_mem_cycloUnits` (`c_n(a) ∈ 𝒟_n`: the
word `(ξ^a−1)(ξ−1)⁻¹` in the generated subgroup, plus global integrality) and (ii)
`norm_cycloUnit_sub_one_lt_one` (the ultrametric estimate `‖c_n(a) − 1‖ < 1` for `a ≡ 1 mod p`). Each of
those is a separate project lemma with its own `/mathlibable` report. Once they are in hand, the body of
`cyclo_mem_cycloTower1` is pure *packaging*: `rw [cycloClosureOne, Subgroup.mem_inf]`,
`rw [cycloClosure, Subgroup.mem_inf]`, `Subgroup.le_topologicalClosure _ hmemD`, and bundling — i.e. two
applications of mathlib's meet-membership primitive and one of its closure-containment primitive, threaded
through the project's pointwise inverse-limit predicate. That is precisely the "1–3 mathlib-call
composition over local definitions" shape the NO-composable bucket exists for. It is consistent with the
sibling reports in this same tower: `cycloTower1`, `cycloClosureOne`, and `cycloTower1_le_unitsTower1` all
landed `NO-composable-from-mathlib`, and `cycloUnits` `BORDERLINE` — none is a mathlib addition.

The theorem is correct, well-named, sorry-free, and the right milestone to keep **in the project** (it is
the §11.3 headline and the input to the Coleman map). It is simply not a mathlib contribution: there is
nothing here to *add* (the reusable kernels `Subgroup.mem_inf` / `Subgroup.le_topologicalClosure` already
exist) and nothing to *generalise* (the objects are project-bespoke; the hypotheses are already minimal).

**WHY not (refactor-actionable detail):**

Mathlib already has the structural building blocks; the residual proof — *after* the two project
content-lemmas — is a ≤3-call composition of them over project-local definitions, so no standalone
mathlib lemma is warranted (and the statement itself is un-stateable in mathlib without the bespoke
towers).

- Mathlib building blocks (the residual glue):
  - `Subgroup.mem_inf` — `.lake/packages/mathlib/Mathlib/Algebra/Group/Subgroup/Lattice.lean`
    (`x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p'`); used twice to split the triple meet
    `(closure ⊓ localUnits) ⊓ localUnitsOne`. Equivalently `inf_le_left`/`inf_le_right`
    (`Mathlib/Order/Lattice.lean`).
  - `Subgroup.le_topologicalClosure` — mathlib's `G ≤ G.topologicalClosure` (closure-containment in a
    topological group); used once for `hmemD : … ∈ cycloUnits p n` ⟹ `… ∈ (cycloUnits p n).topologicalClosure`.
- Project content-lemmas this theorem *depends on* (each separately mathlib-assessed; **not** part of the
  composition, and **not** mathlib-bound either, being about project objects):
  - `cyclo_elems_mem_cycloUnits` (`CyclotomicUnits.lean:421`) — `c_n(a) ∈ 𝒟_n`.
  - `norm_cycloUnit_sub_one_lt_one` (`CyclotomicUnits.lean:376`) — `‖c_n(a) − 1‖ < 1` (T1113).

Composition sketch (≤3 lines of mathlib glue, *given* the two content-lemmas) — shown to make clear the
residual is mechanical, **not** to suggest inlining it (see refactor plan):
```lean
-- given hmemD : (cyclo …).elems n ∈ cycloUnits p n  and  the principal bound,
-- with cycloClosureOne p n = ((cycloUnits p n).topologicalClosure ⊓ localUnits p n) ⊓ localUnitsOne p n:
exact ⟨⟨Subgroup.le_topologicalClosure _ hmemD, hmemloc⟩,
       hmemloc, by rw [hval]; exact norm_cycloUnit_sub_one_lt_one p ha hn ha1⟩
```

Call sites in our project (from Phase 6.0): **K = 1** — `Iwasawa/CyclotomicUnits.lean:498` (feeds the
sibling milestone `cyclo_mem_unitsTower1`).

Refactor plan (honest recommendation — this is a **project-cleanup** decision, not a mathlib one):
  - Option A (keep it — recommended): leave `cyclo_mem_cycloTower1` as the named §11.3 milestone. It is
    the headline result, reads clearly, and its one consumer (`cyclo_mem_unitsTower1`) and the broader
    §12 development (`IwasawaProof/`) treat it as the canonical statement that "the Coleman input is a
    global cyclotomic unit in the principal tower". Naming it is correct project hygiene, even though the
    body is assembly. **Do not inline.**
  - Option B (only if a project cleanup insists on dropping thin assembly wrappers): since K = 1, one
    could inline the assembly at `CyclotomicUnits.lean:498`, folding it into `cyclo_mem_unitsTower1`. This
    is **not recommended** — it would bury the milestone and lose the RJW TeX 3084 anchor for no gain.

Next action for the **mathlib question specifically**: **do not** propose this for mathlib. There is
nothing to add (`Subgroup.mem_inf` / `Subgroup.le_topologicalClosure` already exist) and nothing to
generalise (the towers are project-bespoke; the hypotheses are minimal/correctness-critical). The genuine
content lives in the *dependency* lemmas, which are assessed separately. Keep this milestone project-local
(Option A). No mathlib PR.

---

## Next step

Do not open a mathlib PR. The statement is about project-only objects (`cyclo`, `cycloTower1`,
`cycloClosureOne`, `cycloClosure`, `cycloUnits`, `localUnits`, `localUnitsOne`, `NormCompatUnits` — all
zero mathlib hits), and its residual proof is a ≤3-call composition of mathlib's `Subgroup.mem_inf` and
`Subgroup.le_topologicalClosure` over those definitions, *given* the two project content-lemmas
(`cyclo_elems_mem_cycloUnits`, `norm_cycloUnit_sub_one_lt_one`) where the real mathematics lives. Keep
`cyclo_mem_cycloTower1` as the project-internal §11.3 milestone (RJW TeX 3084); it is the canonical input
to the Coleman map and reads well at its single call site. Direct any mathlib effort instead at general,
reusable nuggets surfaced elsewhere in the file's dependency assessments — not at this assembly milestone.
