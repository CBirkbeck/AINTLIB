"""Shared extraction logic for `formalisation.yaml`.

Both the generator (`gen_formalisation.py`) and the comparator (`check_formalisation.py`)
import this, so the manifest and the check can never drift apart by reading the source
differently — the comparator re-derives the same facts and diffs them against the manifest.

The library is the source of truth. Everything here is derived from the `.lean` files:
declaration names (with their namespace stack), source citations parsed out of docstrings,
and `sorry` status. Nothing is hand-maintained.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

# ---------------------------------------------------------------------------
# Layout
# ---------------------------------------------------------------------------

LIB_DIR_NAME = "Adic spaces"
LIB_NAMESPACE = "«Adic spaces»"
#: third-party code; never part of the formalisation manifest
# `Vendored` is third-party code; `Comparator` is certification scaffolding whose
# challenge files carry INTENTIONAL `sorry`s (pinned statements, not WIP) — neither
# belongs in the library inventory.
EXCLUDED_PARTS = ("Vendored", "Comparator")


def library_root(project_root: Path) -> Path:
    return project_root / LIB_DIR_NAME


def lean_files(project_root: Path) -> list[Path]:
    root = library_root(project_root)
    out = [
        p
        for p in sorted(root.rglob("*.lean"))
        if not any(part in EXCLUDED_PARTS for part in p.relative_to(root).parts)
    ]
    return out


def module_name(project_root: Path, path: Path) -> str:
    """`.../Adic spaces/FJP/FiniteJetMain.lean` -> `«Adic spaces».FJP.FiniteJetMain`."""
    rel = path.relative_to(library_root(project_root)).with_suffix("")
    return ".".join([LIB_NAMESPACE, *rel.parts])


# ---------------------------------------------------------------------------
# Source citations
# ---------------------------------------------------------------------------

#: Bibliography keys used by the manifest. `pattern` finds a citation inside a docstring
#: whose whitespace has already been collapsed to single spaces (docstrings wrap freely,
#: so `Wedhorn\nCor 8.32` must match as `Wedhorn Cor 8.32`).
REFERENCES: dict[str, dict[str, str]] = {
    "wedhorn": {
        "title": "Torsten Wedhorn, *Adic Spaces* (lecture notes)",
        "pattern": (
            r"Wedhorn\s+"
            r"(?:(Definition|Def|Proposition|Prop|Theorem|Thm|Lemma|Lem|Corollary|Cor"
            r"|Remark|Rem|Example|Ex|Section|§)\s*)?"
            r"(\d+(?:\.\d+)*(?:\([^)]{1,6}\))?)"
        ),
    },
    "fjp": {
        "title": "[FJP] — the finite-jet pinching-algebra source paper",
        "pattern": (
            r"\[FJP\]\s+"
            r"(?:(Theorem|Thm|Proposition|Prop|Lemma|Lem|Corollary|Cor|Remark|Rem"
            r"|Example|Ex|Section|§)\s*)?"
            r"(\d+(?:\.\d+)*)"
        ),
    },
    "wp": {
        "title": "[WP] — §6 of the source paper: the weighted-parity (rationally stably "
                 "reduced) example",
        "pattern": (
            r"\[WP\]\s+"
            r"(?:(Theorem|Thm|Proposition|Prop|Lemma|Lem|Corollary|Cor|Remark|Rem"
            r"|Example|Ex|Section|§|Eq|Def|Sec)\s*[.:]?\s*)?"
            r"((?:\d+(?:\.\d+)*)|(?:[a-z]+:[A-Za-z0-9_-]+)|(?:[A-Za-z0-9_]+(?:-[A-Za-z0-9_-]+)+))"
        ),
    },
    "huber": {
        "title": "R. Huber, *Continuous valuations* / *A generalization of formal schemes*",
        "pattern": (
            r"\[(Hu\d?)\]\s+"
            r"(?:(?:Theorem|Thm|Proposition|Prop|Lemma|Lem|Corollary|Cor)\s*)?"
            r"(\d+(?:\.\d+)*)"
        ),
    },
    "stacks": {
        "title": "The Stacks Project",
        "pattern": r"Stacks\s+(?:Tag\s+)?([0-9A-Z]{4})",
    },
}

_CITE_RX = {k: re.compile(v["pattern"], re.I) for k, v in REFERENCES.items()}

#: canonical spelling for the abbreviations above
_KIND_CANON = {
    "def": "Definition", "definition": "Definition",
    "prop": "Proposition", "proposition": "Proposition",
    "thm": "Theorem", "theorem": "Theorem",
    "lem": "Lemma", "lemma": "Lemma",
    "cor": "Corollary", "corollary": "Corollary",
    "rem": "Remark", "remark": "Remark",
    "ex": "Example", "example": "Example",
    "§": "Section", "section": "Section",
}


def parse_citations(docstring: str) -> list[dict[str, str]]:
    """Return the source citations in `docstring`, as `{ref, at, kind?}` records.

    Whitespace is collapsed first: docstrings wrap mid-citation often enough that a
    newline-sensitive pattern silently loses a third of the Wedhorn references.

    The citation **id** is `<ref>:<at>` and deliberately excludes the kind word, so that
    `Wedhorn Lemma 7.31` and a bare `Wedhorn 7.31` are recognised as the same result --
    both spellings occur in this library, and a comparator that treated them as distinct
    would report phantom coverage gaps.
    """
    flat = re.sub(r"\s+", " ", docstring)
    by_id: dict[str, dict[str, str]] = {}
    for key, rx in _CITE_RX.items():
        for m in rx.finditer(flat):
            kind = ""
            if key == "stacks":
                at = m.group(1).upper()
                ref = "stacks"
            elif key == "huber":
                ref, at = "huber", f"{m.group(1)} {m.group(2)}"
            else:
                ref, at = key, m.group(2)
                if m.group(1):
                    kind = _KIND_CANON.get(m.group(1).lower(), m.group(1).title())
            rec = {"ref": ref, "at": at}
            if kind:
                rec["kind"] = kind
            cid = f"{ref}:{at}"
            # a kinded spelling is more informative than a bare number; keep it
            if cid not in by_id or (kind and "kind" not in by_id[cid]):
                by_id[cid] = rec
    return [by_id[k] for k in sorted(by_id)]


def citation_id(rec: dict[str, str]) -> str:
    return f"{rec['ref']}:{rec['at']}"


# ---------------------------------------------------------------------------
# Declaration extraction
# ---------------------------------------------------------------------------

_DECL_RX = re.compile(
    r"^(?P<mods>(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure|class|inductive|example)"
    r"(?:\s+(?P<name>[^\s({\[:]+))?"
)
_NS_OPEN = re.compile(r"^namespace\s+(\S+)")
_NS_CLOSE = re.compile(r"^end\s+(\S+)\s*$")
_SECTION = re.compile(r"^section(?:\s+(\S+))?\s*$")

#: declaration kinds that carry mathematical content worth listing as a result
RESULT_KINDS = {"theorem", "lemma"}


@dataclass
class Decl:
    name: str                       # fully qualified
    kind: str
    module: str
    file: str                       # repo-relative
    line: int                       # 1-indexed
    private: bool
    sorry: bool
    signature: str
    digest: str
    docstring: str
    citations: list[dict[str, str]] = field(default_factory=list)

    @property
    def summary(self) -> str:
        """First sentence of the docstring, markdown stripped, as the informal statement.

        Split on `. ` only, never on a colon: many docstrings here open with
        "The key jet computation ([FJP] Prop 3.1's W -> ...):" and a colon-split truncates
        the statement to its own preamble.
        """
        d = re.sub(r"\s+", " ", self.docstring).strip()
        d = re.sub(r"\*\*(.+?)\*\*", r"\1", d)          # bold
        d = re.sub(r"\$`(.+?)`", r"\1", d)              # verso math (before code spans)
        d = re.sub(r"`([^`]*)`", r"\1", d)              # code spans
        m = re.search(r"\.\s", d)
        s = d[: m.start() + 1] if m else d
        if len(s) > 240:
            s = s[:237].rsplit(" ", 1)[0] + "…"
        return s.strip()


_OPEN = "([{⟨"
_CLOSE = ")]}⟩"


def signature_of(decl_lines: list[str]) -> str:
    """The declaration's statement: everything up to the top-level `:=` (or `where`).

    Bracket depth is tracked rather than splitting on the first `:=`, because binders and
    default arguments (`letI`, `(h : P := by simp)`) contain `:=` inside brackets; a naive
    split silently truncates the statement and the digest then tracks the wrong text.
    """
    depth = 0
    out: list[str] = []
    for line in decl_lines:
        # strip line comments outside brackets; block comments do not occur in signatures
        i = 0
        buf: list[str] = []
        while i < len(line):
            c = line[i]
            if c in _OPEN:
                depth += 1
            elif c in _CLOSE:
                depth = max(0, depth - 1)
            elif depth == 0 and line.startswith("--", i):
                break
            elif depth == 0 and line.startswith(":=", i):
                buf.append(line[:i])
                out.append("".join(buf) if buf else line[:i])
                return re.sub(r"\s+", " ", " ".join(out)).strip()
            i += 1
        out.append(line)
        if depth == 0 and re.search(r"(?:^|\s)where\s*$", line):
            break
    return re.sub(r"\s+", " ", " ".join(out)).strip()


def digest(text: str) -> str:
    import hashlib

    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:12]


def _docstring_above(lines: list[str], idx: int) -> tuple[str, int]:
    """Return (docstring, index of its first line) for the decl starting at `idx`.

    Walks back over attribute lines and `omit`/`include`/`variable`/`set_option ... in`
    modifiers, which legally sit between a docstring and its declaration.
    """
    k = idx - 1
    while k >= 0:
        s = lines[k].strip()
        if not s:
            return "", idx
        if (s.startswith("@[") or s.startswith("omit ") or s.startswith("include ")
                or s.startswith("set_option ") or s.endswith(" in")):
            k -= 1
            continue
        break
    if k < 0 or not lines[k].rstrip().endswith("-/"):
        return "", idx
    end = k
    while k >= 0 and not lines[k].lstrip().startswith("/--"):
        k -= 1
    if k < 0:
        return "", idx
    body = "\n".join(lines[k : end + 1])
    body = re.sub(r"^\s*/--", "", body)
    body = re.sub(r"-/\s*$", "", body)
    return body.strip(), k


def _decl_end(lines: list[str], start: int, is_code: list[bool] | None = None) -> int:
    """Index one past the last line of the declaration beginning at `start`."""
    k = start + 1
    while k < len(lines):
        s = lines[k]
        if is_code is not None and not is_code[k]:
            k += 1
            continue
        if s and not s[0].isspace():
            if (_DECL_RX.match(s) or _NS_OPEN.match(s) or _NS_CLOSE.match(s)
                    or s.startswith(("/--", "/-!", "@[", "end", "section", "variable",
                                     "omit", "include", "open", "namespace", "set_option",
                                     "attribute", "import", "instance", "/-"))):
                break
        k += 1
    return k


def code_line_mask(lines: list[str]) -> list[bool]:
    """`True` for each line that *begins* outside any block comment.

    Without this, docstring prose is parsed as code: this library contains docstrings whose
    continuation lines start at column 0 with "theorem is unsound outside ...",
    "lemma so the chain assembly ...", "structure presheaf is a sheaf ...". Each produced a
    phantom declaration (`ValuationSpectrum.is`, `.so`, `.presheaf`) that then collided with
    a real one. Lean block comments nest, so depth is counted rather than toggled.
    """
    depth = 0
    mask: list[bool] = []
    for line in lines:
        mask.append(depth == 0)
        i = 0
        while i < len(line):
            if line.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if line.startswith("-/", i):
                depth = max(0, depth - 1)
                i += 2
                continue
            if depth == 0 and line.startswith("--", i):
                break                      # line comment: nothing after it is code
            i += 1
    return mask


def extract_file(project_root: Path, path: Path) -> list[Decl]:
    text = path.read_text(errors="replace")
    lines = text.split("\n")
    is_code = code_line_mask(lines)
    mod = module_name(project_root, path)
    try:
        rel = str(path.relative_to(project_root.parents[1]))
    except ValueError:
        rel = str(path)

    ns: list[str] = []
    out: list[Decl] = []
    for i, line in enumerate(lines):
        if not is_code[i]:
            continue
        m = _NS_OPEN.match(line)
        if m:
            ns.extend(m.group(1).split("."))
            continue
        m = _NS_CLOSE.match(line)
        if m:
            parts = m.group(1).split(".")
            if ns[-len(parts):] == parts:
                del ns[-len(parts):]
            continue
        m = _DECL_RX.match(line)
        if not m or not m.group("name"):
            continue
        name = m.group("name")
        if name.startswith("_"):
            continue
        doc, _ = _docstring_above(lines, i)
        end = _decl_end(lines, i, is_code)
        body = "\n".join(lines[i:end])
        sig = signature_of(lines[i:end])
        out.append(
            Decl(
                name=".".join([*ns, name]),
                kind=m.group("kind"),
                module=mod,
                file=rel,
                line=i + 1,
                private="private" in m.group("mods"),
                sorry=bool(re.search(r"(?<![\w'])sorry(?![\w'])", body)),
                signature=sig,
                digest=digest(sig),
                docstring=doc,
                citations=parse_citations(doc),
            )
        )
    return out


def extract_all(project_root: Path) -> list[Decl]:
    out: list[Decl] = []
    for p in lean_files(project_root):
        out.extend(extract_file(project_root, p))
    return out


# ---------------------------------------------------------------------------
# Grouping
# ---------------------------------------------------------------------------

#: `formalisation.yaml` groups. First match wins; `adic-spaces` is the catch-all so that
#: "all of the adic spaces development" is covered rather than only the flagged parts.
GROUPS: list[tuple[str, str, re.Pattern]] = [
    ("fjp", "The finite-jet pinching algebra ([FJP])", re.compile(r"(?:^|\.)FJP\.")),
    ("wp", "The weighted-parity rationally-stably-reduced example ([WP] §6)",
     re.compile(r"(?:^|\.)WP\.")),
    ("scottish-book",
     "The Nonarchimedean Scottish Book — Kedlaya's open-problem list, one module per problem",
     re.compile(r"(?:^|\.)ScottishBook\.")),
    ("examples", "Worked examples and numbered results reduced to concrete rings",
     re.compile(r"(?:^|\.)(Example[A-Za-z0-9]*|Cor\d+|Lemma\d+|Prop\d+|Thm\d+)$")),
    ("adic-spaces", "Core adic-spaces development", re.compile(r".")),
]


def group_of(module: str) -> str:
    for key, _desc, rx in GROUPS:
        if rx.search(module):
            return key
    return "adic-spaces"


# ---------------------------------------------------------------------------
# The Nonarchimedean Scottish Book
# ---------------------------------------------------------------------------

#: `Adic spaces/ScottishBook/<stage>/ProblemNNN.lean`, where the stage records how far the
#: formalisation has gone: `Described` = prose only, `Stated` = a Lean statement exists.
SCOTTISH_DIR = "ScottishBook"

_SB_NUM = re.compile(r"Problem0*(\d+)")
_SB_FIELD = {
    "proposer": re.compile(r"^\*\*Proposer:\*\*\s*(.+?)\s*$", re.M),
    "date": re.compile(r"^\*\*Date:\*\*\s*(.+?)\s*$", re.M),
}
_SB_STATUS = re.compile(r"^##\s*Status\s*$(.*?)(?=^##\s|\Z)", re.M | re.S)


def _sb_literature_status(body: str) -> tuple[str, str]:
    """(verdict, verbatim first sentence) of the `## Status` section.

    Verdict is the status **in the literature**, not in Lean — these are open problems, so a
    `sorry` here is the honest state of mathematics rather than unfinished work, and the two
    must not be conflated.
    """
    m = _SB_STATUS.search(body)
    if not m:
        return "unknown", ""
    text = " ".join(l.strip() for l in m.group(1).strip().split("\n") if l.strip())
    if not text:
        return "unknown", ""
    low = text.lower()
    if low.startswith("resolved") or low.startswith("likely resolved"):
        verdict = "resolved"
    elif low.startswith("partially resolved"):
        verdict = "partial"
    elif low.startswith("open"):
        verdict = "open"
    else:
        verdict = "unknown"
    first = re.split(r"(?<=\.)\s", text)[0]
    return verdict, first[:200]


def scottish_book_problems(project_root: Path, decls: list[Decl] | None = None) -> list[dict]:
    """One record per Scottish Book problem file, sorted by problem number."""
    root = library_root(project_root) / SCOTTISH_DIR
    if not root.is_dir():
        return []
    if decls is None:
        decls = extract_all(project_root)
    per_module: dict[str, list[Decl]] = {}
    for d in decls:
        per_module.setdefault(d.module, []).append(d)

    out: list[dict] = []
    for path in sorted(root.rglob("Problem*.lean")):
        body = path.read_text(errors="replace")
        mod = module_name(project_root, path)
        ds = per_module.get(mod, [])
        num = _SB_NUM.search(path.stem)
        verdict, sentence = _sb_literature_status(body)
        rec = {
            "problem": int(num.group(1)) if num else 0,
            "stage": path.parent.name.lower(),      # described | stated
            "module": mod,
            "literature_status": verdict,
            "declarations": len(ds),
            "with_sorry": sum(d.sorry for d in ds),
            "proved": sum(not d.sorry for d in ds),
        }
        for k, rx in _SB_FIELD.items():
            m = rx.search(body)
            if m:
                rec[k] = m.group(1)
        if sentence:
            rec["status_note"] = sentence
        out.append(rec)
    out.sort(key=lambda r: r["problem"])
    return out
