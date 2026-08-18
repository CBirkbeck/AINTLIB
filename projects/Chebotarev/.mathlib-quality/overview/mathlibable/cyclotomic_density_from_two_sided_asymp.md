# Mathlibable assessment — `Chebotarev.cyclotomic_density_from_two_sided_asymp`

**Verdict: `YES-but-generalise-first`**

> Standard Chebotarev density theorem (cyclotomic case), a major named result absent from
> mathlib — but mathlib-bound only after its bespoke `HasDirichletDensity` foundation lands,
> and the singleton-`σ` / `1/|G|` form should generalise to the conjugacy-class `#A/|G|` form.

---

## 0. Declaration under assessment

- **Qualified name (verified from source):** `Chebotarev.cyclotomic_density_from_two_sided_asymp`
  - `namespace Chebotarev` opened at `Cyclotomic.lean:49`; theorem at `Cyclotomic.lean:962`.
  - The parse hint `Chebotarev.cyclotomic_density_from_two_sided_asymp` is **correct**.
- **Location:** `projects/Chebotarev/CebotarevDensity/Cyclotomic.lean:962`.

### Statement (verbatim shape)

```lean
theorem cyclotomic_density_from_two_sided_asymp
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2)
    (σ : Gal(L/K)) :
    Tendsto
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 ((Nat.card Gal(L/K) : ℝ)⁻¹))
```

### Proof (verbatim, 3 lines)

```lean
  tendsto_ratio_of_log_asymp_numerator _ _ _
    (primeIdealZetaSum_frobeniusFibre_asymp K L m hm σ)
    (primeIdealZetaSum_univ_tendsto_log K)
```

### Mathematical content

`HasDirichletDensity` (`Density.lean:64`) is *definitionally* the `Tendsto` of the ratio
`primeIdealZetaSum S / primeIdealZetaSum univ` to `δ` at `𝓝[>] 1`. So this theorem is literally
"the frobenius-fibre set `{𝔭 : φ_𝔭 = σ}` of `K ⊂ K(μ_m)` has **Dirichlet density `1/|Gal(L/K)|`**".
The immediately-following `Chebotarev.chebotarev_cyclotomic` (`Cyclotomic.lean:982`) is
`:= cyclotomic_density_from_two_sided_asymp K L m hm σ` — i.e. this declaration *is* the
Chebotarev cyclotomic theorem, with `HasDirichletDensity` unfolded to its `Tendsto` definition.

This is the **cyclotomic / abelian case of the Chebotarev density theorem** — itself the
generalisation of Dirichlet's theorem on primes in arithmetic progressions.

---

## 1. Literature search

| Source | Statement found | Standard generality |
|---|---|---|
| Wikipedia, *Chebotarev density theorem* | For `L/K` normal, conjugacy class `A ⊂ Gal(L/K)`: `{𝔭 : Frob_𝔭 = A}` has Dirichlet density `#A / [L:K]`. | Conjugacy-class form; arbitrary Galois `L/K`. |
| Encyclopedia of Mathematics | Dirichlet density `d(M) = lim_{s→1⁺} (Σ_{𝔭∈M} N𝔭⁻ˢ)/(Σ_𝔭 N𝔭⁻ˢ)`; weak form: density `#A/n`. | Exactly the density def used here; class form. |
| Stevenhagen–Lenstra, *Chebotarëv and his density theorem* | Cyclotomic case: Frobenius equidistributes over `G`, density of `{σ_p = σ}` is `1/#G`. | The cyclotomic special case = this theorem. |
| Wolfram MathWorld / Grokipedia / Di Meglio notes / Triantafillou notes | Same — equidistribution among conjugacy classes; density `#A/n`. | Class form, general `L/K`. |
| Sharifi, *Algebraic Number Theory* §7.2.1 (project's cited source, `docs/algnum.pdf` p. 142) | The two-sided log-asymptotic comparison this file formalises; yields density `1/|G|` for the cyclotomic case. | Cyclotomic case (this exact argument). |

**Conclusion:** A canonical, famous named theorem. The maximally-general literature form is the
**conjugacy-class statement for arbitrary Galois `L/K`: density `#A/[L:K]`.** This declaration is
the abelian/cyclotomic special case with `A = {σ}` a singleton (hence `#A = 1`, density
`1/|Gal(L/K)|`), and additionally carries the project artefact `hm : m % 4 ≠ 2`.

---

## 2. Mathlib search (five-method, exhaustive)

Local stale build ⇒ relied on direct source grep over the pinned mathlib tree
(`.lake/packages/mathlib`, pin `d90090f`) + web/leansearch awareness.

1. **`grep` over `Mathlib/NumberTheory`** for `Chebotarev | DirichletDensity | frobeniusClass`
   → **zero hits.**
2. **`grep` over the entire `Mathlib/`** for `DirichletDensity | chebotarev | Dirichlet density`
   → only unrelated **combinatorial "natural density"** TODOs in
   `MeasureTheory/Function/Intersectivity.lean` and `Combinatorics/Schnirelmann.lean`. No
   analytic / prime-ideal Dirichlet density anywhere.
3. **`grep` for `frobeniusClass` / `frobeniusClasses`** across mathlib → **zero hits.** Mathlib has
   no Frobenius-conjugacy-class-of-a-prime API at all.
4. **Concept search** (web "mathlib4 Chebotarev density"): no mathlib implementation surfaces; the
   theorem is simply not in the library.
5. **Building blocks present but not assembled:** mathlib has Dedekind ζ
   (`NumberField.DedekindZeta`), Dirichlet `L`-functions, cyclotomic extensions
   (`IsCyclotomicExtension`), and `NumberField.Ideal` API — but **no Dirichlet density of prime
   ideals**, **no Frobenius-fibre density**, **no Chebotarev**.

**Conclusion:** Neither the theorem nor any more-general form exists in mathlib. Even the
*foundational definition* `HasDirichletDensity` / `primeIdealZetaSum` is project-local
(`Density.lean:50, 64`) and absent from mathlib.

---

## 3. Generality analysis vs. the literature-standard form

- **Underlying object — non-standard, project-local.** `Chebotarev.HasDirichletDensity`
  (`Density.lean:64`) and `Chebotarev.primeIdealZetaSum` (`Density.lean:50`) are bespoke. Mathlib
  has no analytic Dirichlet density of prime ideals. Any mathlib upstreaming must land *these
  definitions first* (they are the natural, literature-matching primitives — Encyclopedia of Math
  gives the identical `lim Σ N𝔭⁻ˢ / Σ N𝔭⁻ˢ` definition).
- **Hypotheses — narrower than the literature.**
  - Restricted to **cyclotomic** `L = K(μ_m)` (abelian `Gal(L/K)`), vs. the literature's arbitrary
    Galois `L/K`.
  - Restricted to a **singleton** `σ` (`ConjClasses.mk σ`), giving density `1/|G|`, vs. the
    literature's general conjugacy class `A` with density `#A/[L:K]`. (In the abelian case classes
    are singletons, so for the cyclotomic case these coincide — but the *target* form mathlib would
    want is the class form.)
  - Carries the artefact hypothesis **`hm : m % 4 ≠ 2`**, a project-internal restriction (tied to
    the `IsCyclotomicExtension {m}` normalisation, not present in the mathematical statement). This
    is exactly the kind of spurious hypothesis a generalisation pass should remove.
- **Density value form.** `(Nat.card Gal(L/K) : ℝ)⁻¹` is correct for the singleton case; the
  general theorem wants `#A / Nat.card Gal(L/K)`.

So relative to the literature this is a **special case along three axes** (cyclotomic vs. general
Galois; singleton vs. class; plus a spurious `m % 4 ≠ 2`). The general Chebotarev theorem is a
known AINTLIB target (the abelian and general cases are being built in sibling files —
`FixedFieldDensity.lean`, `CyclotomicNormResidue.lean`). Pushing the *singleton+cyclotomic+`mod 4`*
form into mathlib as-is would freeze a non-canonical intermediate.

---

## 4. Composition check (≤ 3 mathlib calls?)

**No — not composable from mathlib primitives.** The proof *is* a 3-call composition, but the
composed terms are **project-local, not mathlib**:

```
tendsto_ratio_of_log_asymp_numerator   -- project lemma (Cyclotomic.lean:944), pure real-analysis glue
  (primeIdealZetaSum_frobeniusFibre_asymp …)  -- project, Sharifi 7.2.1(iv-a): the DEEP numerator
                                              --   asymptotic  num(s)/log(1/(s-1)) → 1/|G|
                                              --   (built on character orthogonality, twisted prime
                                              --    sums, Artin L-series nonvanishing — hundreds of
                                              --    lines across this file + ZetaProduct.lean)
  (primeIdealZetaSum_univ_tendsto_log K)      -- project, Sharifi 7.1.12: denominator ~ log(1/(s-1))
```

- `tendsto_ratio_of_log_asymp_numerator` is a genuinely generic, mathlib-flavoured real-analysis
  lemma (if `num/L → c` and `den/L → 1` then `num/den → c`) — *that* leaf is composable from
  mathlib `Tendsto.div` etc. and could even go to mathlib on its own.
- But `primeIdealZetaSum_frobeniusFibre_asymp` is the entire mathematical heart of Chebotarev's
  cyclotomic case and is **not** reachable in ≤3 mathlib calls — it depends on the whole
  project-local apparatus (`HasDirichletDensity`, `twistedPrimeSum`, character orthogonality, Artin
  `L`-series nonvanishing in `ZetaProduct`).

So the theorem is **decidedly not** a trivial mathlib composition. It is a thin **definitional
repackaging** (unfold `HasDirichletDensity`) of a deep, non-mathlib result.

---

## 5. Verdict rationale → `YES-but-generalise-first`

- **Belongs in mathlib in spirit:** Chebotarev's density theorem is a top-tier named theorem (a
  long-standing mathlib wish-list item, the natural successor to Dirichlet's theorem). Its
  cyclotomic case and the `HasDirichletDensity` framework are exactly the kind of content mathlib
  wants. Confirmed **absent** from mathlib by exhaustive grep (no density, no Chebotarev, no
  `frobeniusClass`).
- **Not `NO-mathlib-has-it`:** nothing remotely close exists upstream.
- **Not `NO-composable-from-mathlib`:** the 3-line proof composes *project* lemmas, not mathlib
  ones; the numerator asymptotic is irreducibly deep.
- **Not `YES-add-as-is`:** three issues block a verbatim port —
  1. it depends on project-local `HasDirichletDensity` / `primeIdealZetaSum` that must be upstreamed
     first (the real prerequisite);
  2. the spurious `hm : m % 4 ≠ 2` hypothesis should be discharged/removed;
  3. the statement is the singleton-`σ`, cyclotomic special case — the canonical mathlib target is
     the conjugacy-class form `#A/[L:K]` for general Galois `L/K` (the abelian/general cases are
     already in-flight in sibling files). The frobenius-fibre **density** should also be stated via
     `HasDirichletDensity` (as `chebotarev_cyclotomic` already is) rather than the unfolded
     `Tendsto`-of-ratio shape — this very declaration is just the unfolded twin of
     `chebotarev_cyclotomic`, so the *density-API* sibling is the better mathlib citizen.
- **Not `BORDERLINE-needs-human`:** the call is clear — clearly mathlib-worthy mathematics, clearly
  needs generalisation (framework upstreaming + hypothesis cleanup + class-form statement) before
  it goes in.

**Practical note for upstreaming:** the genuinely-mathlib-ready leaf right now is the generic glue
`tendsto_ratio_of_log_asymp_numerator` (pure `Tendsto` real analysis). The headline result should
wait until the `Chebotarev.HasDirichletDensity` foundation and the *general* Chebotarev statement
are consolidated in AINTLIB; then port the conjugacy-class theorem with `HasDirichletDensity` and
no `mod 4` artefact.
