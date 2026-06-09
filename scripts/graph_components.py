#!/usr/bin/env python3
"""Report connected components of the AINTLIB blueprint dependency graph.

Nodes = blueprint labels (:::definition/lemma_/theorem/corollary "label").
Edges = {uses "label"} occurrences, attributed to the enclosing block's label
(a :::proof shares its theorem's label). Run from the repo root."""
import re, glob
from collections import defaultdict

block_re = re.compile(r':::(definition|lemma_|theorem|corollary|proof)\s+"([^"]+)"')
uses_re  = re.compile(r'\{uses\s+"([^"]+)"\}')

node_chapter, adj = {}, defaultdict(set)
for path in sorted(glob.glob('AINTLIB/Chapters/*.lean')):
    chap = path.split('/')[-1][:-5]
    cur = None
    for line in open(path):
        m = block_re.search(line)
        if m:
            kind, label = m.groups()
            cur = label
            if kind != 'proof':
                node_chapter[label] = chap
            continue
        for um in uses_re.finditer(line):
            if cur:
                adj[cur].add(um.group(1)); adj[um.group(1)].add(cur)

nodes = set(node_chapter)
# orphan {uses} targets (point at a non-existent label) — should be empty
orphans = {t for s in adj for t in adj[s]} - nodes
seen, comps = set(), []
for n in nodes:
    if n in seen:
        continue
    st, comp = [n], set()
    while st:
        x = st.pop()
        if x in seen:
            continue
        seen.add(x); comp.add(x)
        st += [y for y in adj[x] if y not in seen and y in nodes]
    comps.append(comp)
comps.sort(key=len, reverse=True)

print(f"nodes={len(nodes)}  edges={sum(len(v) for v in adj.values())//2}  components={len(comps)}")
print("component sizes (top 12):", [len(c) for c in comps[:12]])
iso = sorted(n for n in nodes if not adj[n])
print(f"isolated nodes ({len(iso)}):")
for n in iso:
    print(f"  {node_chapter.get(n,'?'):28} {n}")
if orphans:
    print(f"\nORPHAN {{uses}} (target label not found) — fix these: {sorted(orphans)}")
