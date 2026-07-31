"""A tiny YAML emitter + loader for `formalisation.yaml`.

`pyyaml` is not installed in this workspace, and the manifest has to round-trip reliably
in whatever environment the check runs in. So:

* if `pyyaml` is importable it is used for loading (it is the reference implementation);
* otherwise the loader here reads back the **restricted subset** the emitter produces.

The subset is deliberately small — block mappings, block sequences, and scalars — and the
loader raises on anything outside it rather than guessing. A silent misparse in a drift
checker is worse than a crash: it would report "no drift" on a file it did not understand.
"""
from __future__ import annotations

import re
from typing import Any

try:  # pragma: no cover - environment dependent
    import yaml as _pyyaml
except ImportError:  # pragma: no cover
    _pyyaml = None


# ---------------------------------------------------------------------------
# Emitting
# ---------------------------------------------------------------------------

#: plain (unquoted) scalars must not be confusable with numbers, booleans, null, or with
#: YAML structure. Anything else gets single-quoted.
_PLAIN_OK = re.compile(r"^[A-Za-z_][A-Za-z0-9_.\-/«»]*$")
_RESERVED = {"true", "false", "yes", "no", "on", "off", "null", "~", ""}


def _scalar(value: Any) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if value is None:
        return "null"
    s = str(value)
    if _PLAIN_OK.match(s) and s.lower() not in _RESERVED:
        return s
    # single quotes: only `'` needs escaping, and no backslash processing happens inside,
    # which matters because these strings are full of Lean/LaTeX backslashes.
    return "'" + s.replace("'", "''") + "'"


def dump(data: Any, indent: int = 0) -> str:
    """Emit `data` as block-style YAML. Only dict / list / scalar are supported."""
    pad = "  " * indent
    out: list[str] = []
    if isinstance(data, dict):
        if not data:
            return pad + "{}"
        for k, v in data.items():
            if isinstance(v, (dict, list)) and v:
                out.append(f"{pad}{_scalar(k)}:")
                out.append(dump(v, indent + 1))
            elif isinstance(v, (dict, list)):
                out.append(f"{pad}{_scalar(k)}: " + ("{}" if isinstance(v, dict) else "[]"))
            else:
                out.append(f"{pad}{_scalar(k)}: {_scalar(v)}")
        return "\n".join(out)
    if isinstance(data, list):
        if not data:
            return pad + "[]"
        for item in data:
            if isinstance(item, dict):
                if not item:
                    out.append(f"{pad}- {{}}")
                    continue
                body = dump(item, indent + 1).split("\n")
                # hoist the first key onto the dash line
                out.append(f"{pad}- " + body[0].lstrip())
                out.extend(body[1:])
            elif isinstance(item, list):
                raise ValueError("nested bare lists are outside the supported subset")
            else:
                out.append(f"{pad}- {_scalar(item)}")
        return "\n".join(out)
    return pad + _scalar(data)


# ---------------------------------------------------------------------------
# Loading
# ---------------------------------------------------------------------------

def _unscalar(tok: str) -> Any:
    tok = tok.strip()
    if tok.startswith("'") and tok.endswith("'") and len(tok) >= 2:
        return tok[1:-1].replace("''", "'")
    if tok.startswith('"') and tok.endswith('"') and len(tok) >= 2:
        return tok[1:-1].encode().decode("unicode_escape")
    if tok == "true":
        return True
    if tok == "false":
        return False
    if tok in ("null", "~"):
        return None
    if tok == "[]":
        return []
    if tok == "{}":
        return {}
    if re.fullmatch(r"-?\d+", tok):
        return int(tok)
    return tok


def _split_kv(s: str) -> tuple[str, str] | None:
    """Split `key: value` outside quotes. Returns None when there is no top-level colon."""
    q: str | None = None
    i = 0
    while i < len(s):
        c = s[i]
        if q:
            if c == q:
                if q == "'" and i + 1 < len(s) and s[i + 1] == "'":
                    i += 2
                    continue
                q = None
        elif c in "'\"":
            q = c
        elif c == ":" and (i + 1 == len(s) or s[i + 1] == " "):
            return s[:i], s[i + 1:]
        i += 1
    return None


class MiniYamlError(ValueError):
    pass


def _parse_block(lines: list[tuple[int, int, str]], pos: int, indent: int) -> tuple[Any, int]:
    """Parse one block at `indent`. `lines` are (lineno, indent, text) with blanks removed."""
    if pos >= len(lines):
        return None, pos
    _, ind, text = lines[pos]
    if ind < indent:
        return None, pos

    if text.startswith("- "):
        items: list[Any] = []
        while pos < len(lines):
            lineno, ind2, text2 = lines[pos]
            if ind2 < indent or not text2.startswith("- "):
                break
            if ind2 > indent:
                raise MiniYamlError(f"line {lineno}: unexpected indent in sequence")
            rest = text2[2:]
            kv = _split_kv(rest)
            if kv is None:
                items.append(_unscalar(rest))
                pos += 1
                continue
            # a mapping whose first key sits on the dash line; its remaining keys are
            # indented by exactly the dash width (2)
            synthetic = [(lineno, indent + 2, rest)]
            pos += 1
            while pos < len(lines) and lines[pos][1] >= indent + 2 and not (
                lines[pos][1] == indent and lines[pos][2].startswith("- ")
            ):
                if lines[pos][1] < indent + 2:
                    break
                synthetic.append(lines[pos])
                pos += 1
            val, used = _parse_block(synthetic, 0, indent + 2)
            if used != len(synthetic):
                raise MiniYamlError(f"line {lineno}: trailing content in sequence item")
            items.append(val)
        return items, pos

    mapping: dict[str, Any] = {}
    while pos < len(lines):
        lineno, ind2, text2 = lines[pos]
        if ind2 < indent:
            break
        if ind2 > indent:
            raise MiniYamlError(f"line {lineno}: unexpected indent in mapping")
        if text2.startswith("- "):
            break
        kv = _split_kv(text2)
        if kv is None:
            raise MiniYamlError(f"line {lineno}: not a mapping entry: {text2!r}")
        key, raw = kv
        key = str(_unscalar(key))
        pos += 1
        if raw.strip():
            mapping[key] = _unscalar(raw)
            continue
        if pos < len(lines) and lines[pos][1] > indent:
            child, pos = _parse_block(lines, pos, lines[pos][1])
            mapping[key] = child
        elif pos < len(lines) and lines[pos][1] == indent and lines[pos][2].startswith("- "):
            child, pos = _parse_block(lines, pos, indent)
            mapping[key] = child
        else:
            mapping[key] = None
    return mapping, pos


def load(text: str) -> Any:
    if _pyyaml is not None:
        return _pyyaml.safe_load(text)
    rows: list[tuple[int, int, str]] = []
    for n, raw in enumerate(text.split("\n"), 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        rows.append((n, len(raw) - len(raw.lstrip()), raw.strip()))
    if not rows:
        return None
    value, used = _parse_block(rows, 0, rows[0][1])
    if used != len(rows):
        raise MiniYamlError(f"unparsed content from line {rows[used][0]}")
    return value
