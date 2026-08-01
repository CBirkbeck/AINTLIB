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
