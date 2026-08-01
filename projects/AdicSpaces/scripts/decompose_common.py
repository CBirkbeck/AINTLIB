#!/usr/bin/env python3
"""Filters every decompose ranking must apply, in one place.

Written because each new ranking tool in this campaign started by silently
re-acquiring the previous one's filters, and each omission was invisible until
its output was read against the actual files:

  decompose_rank v1  assumed a 4-line preamble        -> 63-line helper proposed
  decompose_rank v2  measured preamble above the      -> wrong helper sized
                     FIRST bullet, not the chosen one
  decompose_rank v3  treated bullets as partitioning  -> 1-line bullet scored 22
  decompose_rank v4  counted carried `set` lines free -> 51-line helper ranked top
  decompose_rank v5  scored the call site at 1 line   -> parent 52, not 47
  promote_rank   v1  listed Vendored/ and ignored     -> out-of-scope target at
                     preamble entirely                   rank 5

None of these were vigilance failures; they were a shared concern re-implemented
per tool. Import from here instead.
"""
import re

ID = re.compile(r"[^\W\d][\w'ₐ-ₜ₀-₉]*", re.UNICODE)
NOISE = {'rfl', 'this', '_', 'Set', 'Type', 'Prop', 'fun', 'with', 'at', 'in',
         'to', 'and', 'or', 'by', 'from'}
BUDGET = 50


def ind(s):
    return len(s) - len(s.lstrip())


def in_scope(rec):
    """Vendored/ is third-party; sorry-bearing proofs are the producer's WIP."""
    return not rec['sorry'] and not rec['file'].startswith('Vendored/')


def boilerplate(body, upto=None):
    """Total lines of `letI`/`haveI` instance blocks (multi-line blocks included).

    Any extracted helper must reproduce these for its statement to elaborate,
    and under cluster-promotion each promoted lemma needs its own copy — so this
    multiplies rather than adds.
    """
    end = len(body) if upto is None else upto
    n, k = 0, 0
    while k < end:
        if body[k].strip().startswith(('letI', 'haveI')):
            bi = ind(body[k])
            n += 1
            k += 1
            while k < end and body[k].strip() and ind(body[k]) > bi:
                n += 1
                k += 1
        else:
            k += 1
    return n


def block_extent(body, start, base):
    """A block runs to the first line at indent <= base. Bullets and `have`s do
    NOT partition a proof: `· simp` is one line and the tactics after it are the
    mainline resuming at the same column."""
    j = start + 1
    while j < len(body) and (not body[j].strip() or ind(body[j]) > base):
        j += 1
    return j


def call_cost(n_args):
    """The extracted block is replaced by a CALL, not by one line: it passes
    every promoted local and wraps at roughly four arguments per line. An
    explicit type ascription adds ~3 more, so prefer `have h := f a b c`."""
    return 1 + n_args // 4


def carried_lines(body, upto, used, kinds):
    """Lines of `set`/`let` definitions that must travel into the helper."""
    n = 0
    for k, l in enumerate(body[:upto]):
        if re.match(r"^\s*(set|let)\b", l):
            nm = ID.findall(re.split(r":=|:", l.strip())[0])
            if any(x in used and kinds.get(x) == 'set' for x in nm):
                bi = ind(l)
                n += 1
                k2 = k + 1
                while k2 < upto and body[k2].strip() and ind(body[k2]) > bi:
                    n += 1
                    k2 += 1
    return n


def fits(body_size, boil, carried=0):
    """The 50-line rule is on proof BODIES, not declarations — signature length
    does not count against a helper."""
    return body_size + boil + carried <= BUDGET


# ---------------------------------------------------------------------------

EXPLICIT_VAR = __import__('re').compile(r"^variable\s*[^\[]*\(")


def explicit_section_vars(path):
    """Explicit (parenthesised) `variable` binders in a file.

    A hoisted helper's argument list is (explicit section variables in scope) ++
    (promoted locals). The section prefix never appears in the proof body, so
    nothing in the lifted text hints at it, and the resulting errors name
    something else entirely -- `failed to synthesize instance` at the call, or
    `Application type mismatch` on the first real argument.

    Cost so far: three separate builds (ChartData's `p F ϖ`, FiniteJetChart's
    `F` twice). The recipe already said to grep for this before writing a call;
    saying it was not enough, so it is a function now.
    """
    out = []
    for line in open(path).read().split("\n"):
        if line.startswith("variable") and EXPLICIT_VAR.match(line):
            out.append(line)
    return out


def explicit_section_prefix(lines, decl_index, used_text):
    """Ordered EXPLICIT section variables that a helper at `decl_index` will bind.

    Two filters, both necessary:

      * IN SCOPE -- tracked below, with the reversion rule.
      * ACTUALLY USED -- Lean auto-includes only the section variables a
        declaration mentions. `CurveObject` has `(p) (F) (ϖ)` all in scope, but a
        helper whose statement says only `frobPow p F …` binds `p F` and NOT `ϖ`,
        so the call is `lem p F …`. Pass the helper's full text as `used_text`.

    A lifted helper's argument list is this prefix ++ the promoted locals, so a
    derived call that starts at the locals puts the first local where the first
    section variable belongs. Symptom: `Application type mismatch` naming an
    argument you did think about (`k : ℤ` where `p : ℕ` was expected), never the
    prefix you forgot.

    Two scoping rules this tracks, both learned by paying for them:

      * `variable {A}` REVERTS when its namespace/section closes. StructureSheaf
        declares `(A : Type u)` at namespace level, `{A}` inside `namespace
        StructureSheaf`, and `end StructureSheaf` restores A to EXPLICIT -- so a
        declaration 500 lines later needs `A` passed positionally even though a
        `variable {A}` is plainly visible above it.
      * a later `variable (A)` re-explicits a previously-implicit name.

    Seven builds across this campaign, in two shapes: an explicit variable needs
    prefixing at the call, an unused one needs `omit` on the declaration.
    """
    scopes = [[]]          # stack of (name, explicit) lists, one frame per open scope
    for i in range(decl_index):
        s = lines[i].strip()
        if s.startswith(("namespace ", "section")):
            scopes.append([])
        elif s.startswith("end") and len(scopes) > 1:
            scopes.pop()
        elif s.startswith("variable"):
            # strip instance binders: `[Fact (Nat.Prime p)]` is not a name binder,
            # and its inner parens otherwise parse as one (yielding `Nat.Prime`).
            stripped = re.sub(r"\[[^\]]*\]", " ", lines[i])
            for m in re.finditer(r"([({])([^:()}{]*?)(?::|\})", stripped):
                names = [n for n in m.group(2).split() if ID.fullmatch(n)]
                if not names:
                    continue
                scopes[-1].append((names, m.group(1) == "("))
            # `variable (A)` / `variable {A}` re-declare visibility with no type
            for m in re.finditer(r"([({])\s*([^:()}{]+?)\s*[)}]", stripped):
                names = [n for n in m.group(2).split() if ID.fullmatch(n)]
                if names:
                    scopes[-1].append((names, m.group(1) == "("))
    seen, order = {}, []
    for frame in scopes:
        for names, explicit in frame:
            for n in names:
                seen[n] = explicit
                if n not in order:
                    order.append(n)
    return [n for n in order
            if seen.get(n) and re.search(rf"(?<![\w']){re.escape(n)}(?![\w'])", used_text)]



def assert_statement_complete(first_line, sliced_stmt):
    """A lifted statement fragment must not begin mid-binder.

    When a `have NAME : <TYPE>` is promoted, the quantifier prefix usually lives
    ON the `have` line, which is exactly the line replaced by the new signature.
    Slicing "the lines below it" silently drops the binders, and the failure
    surfaces as a tactic error inside the body -- `introN failed: no additional
    binders`, or `induction: major premise is not an inductive type` -- naming
    the tactic rather than the missing quantifier.

    Two occurrences: hmain in TateAlgebra, hpieces in WedhornCechAcyclicity.
    Both were written up as a lesson and neither was encoded, so here it is.

    Pass the original `have` line and the statement lines you sliced.
    """
    import re
    head = first_line.split(":", 1)[1] if ":" in first_line else ""
    lost = [q for q in ("∀", "∃") if q in head and not any(q in s for s in sliced_stmt)]
    if lost:
        raise AssertionError(
            f"statement slice dropped binder(s) {lost} that lived on the `have` "
            f"line: {first_line.strip()[:80]!r}")
    return True



CONTEXT_FREE_RHS = re.compile(r":=\s*(‹[^›]+›\.[\w'.]+|[\w'.]+)\s*$")


def obtain_is_carryable(line, bound=None):
    """Can this `obtain` be CARRIED into a helper verbatim?

    The cost model prices `obtain`-bound locals at 3 because their types appear
    nowhere. That is only true when the destructuring depends on the proof
    context. When the right-hand side names just an instance or a nullary
    constant, carrying the single `obtain` line into the helper supplies the
    locals AND their types -- exactly what carrying a `set` line does, and what
    carrying a `rw ... at` does for a mutated hypothesis.

    Verified on `le_chain_of_nhds_preimage_subset`, where carrying

        obtain ⟨π, hπ_nil⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit

    turned two cost-3 locals into one line and made a rejected target viable.
    """
    m = CONTEXT_FREE_RHS.search(line) if re.match(r"\s*obtain\b", line) else None
    if not m:
        return False
    # A bare identifier on the RHS may be a GLOBAL (carryable) or a local bound
    # earlier in this proof (not carryable -- carrying the line would reference
    # something the helper does not have). The line alone cannot distinguish
    # them, so the caller must pass what is bound above.
    head = m.group(1)
    if head.startswith("‹"):
        return True
    return head.split(".")[0] not in (bound or ())


def insert_point(lines, decl_index):
    """Where to insert a helper so it lands ABOVE the declaration's header.

    A declaration's header is docstring + attributes + `... in` modifiers, and
    the docstring may contain BLANK LINES -- which is what broke three separate
    hand-rolled anchors in this campaign (each walked up "while non-blank" and
    halted inside the docstring, inserting the helper into the comment).

    Robust rule: skip blanks; if the first non-blank line above closes a
    docstring (`-/`), scan back to the line that opens it (`/--` or `/-!`);
    then keep skipping attribute and `... in` modifier lines.
    """
    i = decl_index
    while i > 0:
        j = i - 1
        while j > 0 and not lines[j].strip():
            j -= 1
        if j < 0:
            break
        prev = lines[j]
        if prev.rstrip().endswith("-/"):
            while j > 0 and not lines[j].lstrip().startswith(("/--", "/-!")):
                j -= 1
            i = j
            continue
        if prev.lstrip().startswith("@[") or prev.rstrip().endswith(" in"):
            i = j
            continue
        break
    return i



def lift_have(lines, decl_start, decl_end, name, params, new_name=None):
    """Lift `have <name> : <stmt> := by <body>` out as a standalone theorem.

    Returns (call_line, helper_lines, i, j) where lines[i:j] is the block to
    replace with `call_line`. Does NOT mutate `lines`.

    Three things this gets right that hand-written versions kept getting wrong:

    1. THE BODY STARTS AFTER THE LINE ENDING `:= by`, not after the `have` line.
       A `have`'s statement wraps freely, and slicing at the `have` line silently
       duplicates the continuation into the body (15 errors, TateAlgebraTopology).

    2. THE PARAMETER BLOCK GETS ITS OWN LINES. Splicing multi-line `params` into
       `have NAME :` in place concatenates the LAST param line with whatever
       followed the `:` -- the start of the conclusion -- reliably producing a
       ~110-column line. Hit three times (hhead_lem 109, hpert_lem 111) before
       being fixed here rather than patched per site.

    3. THE BODY IS DEDENTED BY THE `have`'s OWN INDENT, so a prelude the caller
       prepends at column 2 lines up with it. Mixing a column-2 prelude with a
       column-4 body makes Lean read the body as an argument to the prelude's
       last term (`Function expected at ...`).

    `params` is a LIST OF BINDER LINES, e.g.

        ["(D : RationalLocData A) {m : ℕ}",
         "(aI : Ideal ↥(restrictedMvPowerSeriesSubring m A))"]

    not one concatenated string. Taking a string invited exactly the bug this
    function exists to prevent: two groups joined without a separator produced a
    155-column line (three such, up to 189, in tate_backward_exists). Each entry
    is emitted on its own line at 4-space indent.

    The CALL LINE is derived from the same list -- binder names are read back out
    of `params`, so the argument order cannot drift from the signature. Writing
    the call by hand is how `Φ` ended up in `ψ`'s position on that same target.
    Instance binders `[...]` and implicit `{...}` are skipped; explicit `(x y : T)`
    contributes `x y`.

    The caller still supplies `params`, because the dependency list is the one
    part that cannot be derived from the source. Keeping the CONCLUSION verbatim
    is what makes the body transplant unmodified -- change it only deliberately.
    """
    if isinstance(params, str):
        raise TypeError("params must be a list of binder lines, not a string")
    i = next(k for k in range(decl_start, decl_end)
             if lines[k].lstrip().startswith("have " + name + " ")
             or lines[k].lstrip().startswith("have " + name + ":"))
    base = ind(lines[i])
    j = i + 1
    while j < decl_end and (not lines[j].strip() or ind(lines[j]) > base):
        j += 1
    by = next(k for k in range(i, j) if lines[k].rstrip().endswith(":= by"))
    stmt = [l[base:] if len(l) > base else l for l in lines[i:by + 1]]
    concl = stmt[0].split(":", 1)[1].lstrip()          # text after `have NAME :`
    head = [f"private theorem {new_name or (name + '_lem')}"]
    head += ["    " + p.strip() for p in params]
    head[-1] += " :"
    rest = ([("    " + concl)] if concl else []) + stmt[1:]
    body = [l[base:] if len(l) > base else l for l in lines[by + 1:j]]
    helper = head + rest + body
    # The call is (explicit section vars the helper will bind) ++ (supplied binders).
    # Omitting the first half puts the first local where a section variable belongs
    # and reports `Application type mismatch` on an argument you did think about.
    prefix = explicit_section_prefix(lines, decl_start, "\n".join(helper))
    args = " ".join(prefix + explicit_binder_names(params))
    call = f"{' ' * base}have {name} := {new_name or (name + '_lem')} {args}".rstrip()
    return (call, helper, i, j)


def explicit_binder_names(params):
    """Names bound by `(x y : T)` groups, in order; `[...]`/`{...}` are skipped.

    Only depth-0 parentheses start a binder group -- `(aI : Set ...)` occurring
    inside another binder's TYPE is not one. Reading such an inner ascription as a
    binder is what made me report a phantom duplicate `aI` in tate_backward_exists.
    """
    text = " ".join(params)
    names, depth, i = [], 0, 0
    while i < len(text):
        c = text[i]
        if c in "([{":
            if c == "(" and depth == 0:
                close, d = i, 0
                for k in range(i, len(text)):
                    if text[k] in "([{":
                        d += 1
                    elif text[k] in ")]}":
                        d -= 1
                        if d == 0:
                            close = k
                            break
                group = text[i + 1:close]
                if ":" in group:
                    names += group.split(":", 1)[0].split()
                i = close + 1
                continue
            depth += 1
        elif c in ")]}":
            depth -= 1
        i += 1
    return names


def parent_binders(lines, decl_index, names):
    """Exact source text of the parent's binders for `names`, in signature order.

    The one part of an extraction still typed by hand is the dependency list, and
    it is where the errors are. Four of six consecutive build failures were here:

      hDeq        declared `sum = iterated`; the producer gives `iterated = sum`
      hnoeth      `RestrictedMvPowerSeries.restrictedMvPowerSeriesSubring 2 ↥P.A₀`
                  -- wrong namespace AND wrong construction; it is
                  `TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition`
      hcont_forward  domain given as `↥(TateAlgebra₂ B)`; it is the QUOTIENT
      hφb         omitted entirely (it is a section variable, needs `include`)

    Every one of those types was sitting in the parent's signature, ten lines above
    the block being lifted. Copy, do not reconstruct.

    Returns a list of binder strings ready to pass as `lift_have`'s `params`;
    unmatched names are reported so a typo does not silently drop a hypothesis.
    """
    by = next(k for k in range(decl_index, len(lines))
              if lines[k].rstrip().endswith(":= by"))
    sig, depth, cur = [], 0, []
    for k in range(decl_index, by + 1):
        for ch in lines[k]:
            if ch in "([{":
                if depth == 0:
                    cur = [ch]
                    depth += 1
                    continue
                depth += 1
            elif ch in ")]}":
                depth -= 1
                if depth == 0:
                    cur.append(ch)
                    sig.append("".join(cur))
                    cur = []
                    continue
            if depth:
                cur.append(ch)
        if depth:
            cur.append(" ")
    out, missing = [], []
    for n in names:
        hit = next((b for b in sig
                    if re.match(rf"[\(\{{\[]\s*(?:[\w'ₐ-ₜ₀-₉]+\s+)*{re.escape(n)}\b", b)), None)
        if hit is None:
            missing.append(n)
        else:
            out.append(re.sub(r"\s+", " ", hit))
    if missing:
        raise KeyError(f"not binders of this declaration: {missing}")
    return out
