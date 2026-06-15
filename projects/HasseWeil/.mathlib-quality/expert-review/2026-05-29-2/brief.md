# Review brief (round 8, follow-up) — Leaf 2: your "Option B" for `deg(1−π) = #E(𝔽_q)` needs a correction

*Prepared 2026-05-29 for the same arithmetic-geometry reviewer as rounds 1–7. Self-contained; no repository access required. This is a short follow-up to your round-7 reply, on **Q3 / Leaf 2** only.*

---

## 1. Recap and what we did

In round 7 you advised, for **Leaf 2** (`deg(1−π) = #E(𝔽_q)`, the V.1.3 leaf), to use the **separable-isogeny fibre count** ("Option B"): since `1−π` is separable it is unramified everywhere (every ramification index `e_P = 1`), so the fundamental identity `Σ_{P} e_P f_P = deg` collapses to `Σ f_P = deg`, and over `𝔽̄_q` every `f_P = 1`, giving `#fibre = deg = #ker = #E(𝔽_q)`.

We attempted exactly this. **We shipped the easy half, axiom-clean:**
$$\#E(\mathbb{F}_q) \;\le\; \deg(1-\pi).$$
(The kernel points inject into the set of places over the base place, contributing `Σ e_P f_P = 2·#E(𝔽_q)`, while the total is `2·\deg(1−π)`; monotonicity gives `≤`.)

But the construction surfaced a correction to the mechanism.

## 2. Correction: "separable ⇒ `e_P = 1`" does **not** apply at the level we count

In our setup the places we sum over are the places of `K(E)` lying over the rational place of the **degree-2 subfield** `K(x)` pulled back along `1−π` — i.e. over `K((1−π)^*x)`. That tower has degree
$$[K(E) : K((1-\pi)^*x)] \;=\; [K(E):K(x)] \cdot \deg(1-\pi) \;=\; 2\,\deg(1-\pi),$$
and the **kernel places genuinely have ramification index `e = 2`** — they sit under the double pole of `x` at `O` (`\operatorname{ord}_O x = -2`). So unramifiedness (`e_P = 1`) is simply **false** at this level; the "Option B" collapse `Σ e_P f_P → Σ f_P` does not happen.

The real content is the **residue-degree** side: we need every such place to have **`f_P = 1`** (residue field `= 𝔽_q`, i.e. the closed point is `𝔽_q`-rational). Concretely the open residual is the reverse inequality
$$\deg(1-\pi) \;\le\; \#E(\mathbb{F}_q),$$
which is equivalent to:
$$\boxed{\text{every closed point of } E \text{ over the } O\text{-place has residue degree } 1 \text{ (is } \mathbb{F}_q\text{-rational).}}$$

## 3. Why this is *mathematically* true, and exactly where the *formalisation* gap is

It is true: the **geometric** fibre of `1−π` over `O` is, by definition, `\ker(1−π) = \{P \in E(\overline{\mathbb{F}_q}) : \pi P = P\}`, i.e. precisely the **Frobenius-fixed** geometric points — all of which are `𝔽_q`-rational. A closed point of `E/\mathbb{F}_q` of degree `f` is a Frobenius-orbit of `f` conjugate geometric points; if every geometric point in the orbit is Frobenius-*fixed*, the orbit has size `1`, so `f = 1`. Since *all* geometric points in this fibre are Frobenius-fixed, *every* closed point over `O` has `f = 1`. Done — geometrically.

The **formalisation gap** is exactly the bridge between the two languages:
- the "places over `(X)`" we can count (closed points / function-field valuations of `K(E)`), and
- the "geometric kernel points" `\ker(1−π)` (Frobenius-fixed `\overline{\mathbb{F}_q}`-points),

i.e. the **closed-point ↔ Galois-orbit-of-geometric-points correspondence over a finite field**. The project has the function-field/places side and the geometric kernel side, but not the dictionary that says "a place over `O` has residue degree 1 because its geometric points lie in `\ker(1−π)` and are therefore Frobenius-fixed." Mathlib (verified) has no curve-level closed-point/geometric-point machinery to lean on here. (We also confirmed a purely cardinality-based "squeeze" is **circular**: the only handle on `[K(E):K((1−π)^*x)]` is the same fundamental identity, so any point-count just reproduces the goal.)

## 4. The question

**Q (round 8).** Given that the geometric fibre of `1−π` over `O` is *by construction* entirely Frobenius-fixed (`= \ker(1−π) \subseteq E(\mathbb{F}_q)`), what is the **cleanest formalisation route** to "every closed point (place) of `E` over the `O`-place has residue degree `1`"?

In particular:
1. Is the right tool the **closed-point ↔ Frobenius-orbit** correspondence (each closed point of degree `f` = a size-`f` Frobenius orbit of geometric points; all-fixed ⇒ size 1 ⇒ `f = 1`)? If so, is there a standard, lightweight way to set this up at the **function-field** level (places of `K(E)` ↔ Frobenius orbits on `E(\overline{\mathbb{F}_q})`) without building scheme-theoretic closed-point infrastructure?
2. Or is there a route that bypasses residue degrees entirely — e.g. proving `\deg(1-\pi) \le \#E(\mathbb{F}_q)` directly from `\ker(1-\pi) = E(\mathbb{F}_q)` plus separability, via a **separable ⇒ `#(geometric fibre)` = degree** theorem applied over `\overline{\mathbb{F}_q}` (base-change to `\overline{\mathbb{F}_q}`, count the genuinely-étale fibre there, then descend using that all the points are already `\mathbb{F}_q`-rational)? Does base-changing to `\overline{\mathbb{F}_q}` (where `e = f = 1` genuinely and your Option-B mechanism *does* work) and descending look cheaper than the closed-point dictionary?
3. Is there a Silverman/textbook statement of III.4.10(a) whose proof, specialised to `1−π` over a finite field, makes the `f_P = 1` step trivial (rather than the `e_P = 1` step)?

We are otherwise in good shape: `pointCount ≤ deg(1−π)` is shipped, and the parallel **Leaf 1** (the restricted dual `(rπ−s)^ = rV−s` on the Frobenius plane, per your round-7 Q2) is the alternative near-term target and has none of this Galois-descent difficulty.

## 5. Metadata
- Project: formal Hasse bound for `E/\mathbb{F}_q` (Lean 4 / mathlib). Build green.
- Round-7 actions taken: narrowed Leaf 1 to the restricted Frobenius-plane dual; superseded the Sinf pole-locus detour with the separable-fibre-count plan; shipped `pointCount ≤ deg(1−π)` and pinned the residual as above.
- Prepared 2026-05-29 (follow-up, same day as round 7).
