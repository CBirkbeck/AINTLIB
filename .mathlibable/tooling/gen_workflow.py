#!/usr/bin/env python3
"""Generate a self-contained mathlibable-batch workflow .js with the batch embedded.
Usage: gen_workflow.py <Project> <batch_json> <out_js>"""
import json, sys

PROJ, BATCH_JSON, OUT = sys.argv[1], sys.argv[2], sys.argv[3]
REFS = "/Users/mcu22seu/.claude/plugins/cache/mathlib-quality-plugins/mathlib-quality/0.50.0/skills/mathlib-quality/references"
batch = json.load(open(BATCH_JSON))
WL_LITERAL = json.dumps(batch, ensure_ascii=False)

JS = '''export const meta = {
  name: 'mathlibable-batch',
  description: 'Run full /mathlib-quality:mathlibable per declaration over one batch; write reports + return five-bucket verdicts',
  phases: [
    { title: 'Assess', detail: 'one /mathlibable agent per declaration (bounded concurrency)' },
  ],
}

const PROJECT = %PROJECT%
const REFS = %REFS%
const WL = %WL%
const RDIR = `projects/${PROJECT}/.mathlib-quality/overview/mathlibable`

const SCHEMA = {
  type: 'object',
  additionalProperties: false,
  properties: {
    base: { type: 'string' },
    qual: { type: 'string' },
    bucket: { type: 'string', enum: ['YES-add-as-is', 'YES-but-generalise-first', 'NO-mathlib-has-it', 'NO-composable-from-mathlib', 'BORDERLINE-needs-human'] },
    rationale: { type: 'string' },
    report_path: { type: 'string' },
  },
  required: ['base', 'qual', 'bucket', 'rationale'],
}

function promptFor(d) {
  const report = `${RDIR}/${d.qual}.md`
  return `You are assessing ONE Lean declaration for mathlib-worthiness in the AINTLIB repo.

Working directory: /Users/mcu22seu/Documents/GitHub/aintlib-main  (git branch: main)
Target (qualified name): \\`${d.qual}\\`
Source location: ${d.file}:${d.line}  (kind: ${d.kind})

TASK: Run the \\`/mathlib-quality:mathlibable\\` skill on this single declaration — Mode A, the full 10-phase workflow with the exhaustive 9-channel literature search. Invoke it via the Skill tool:
    Skill(skill="mathlib-quality:mathlibable", args="${d.qual} --refs=${REFS}")
Follow the skill's phases; do not skip the literature or mathlib search.

BUILD NOTE: \\`lake build\\` may be stale/slow here. Do NOT block on a full build — read the declaration and its dependencies directly from source and reason from there, exactly as the skill's Phase 0 fallback allows. Record "build not re-run; reasoned from source" in the baseline.

OUTPUT — two things:
1. Write the skill's full Phase-8 report to:
   ${report}
   The H1 title MUST contain the qualified name in backticks, and the report MUST state the final five-bucket verdict.
2. Return the structured verdict via the StructuredOutput tool: base="${d.qual}", qual="${d.qual}", the chosen bucket, a <=140-char rationale, and report_path="${report}".`
}

phase('Assess')
const CHUNK = 5
const results = []
for (let i = 0; i < WL.length; i += CHUNK) {
  const chunk = WL.slice(i, i + CHUNK)
  const out = await parallel(chunk.map(d => () =>
    agent(promptFor(d), {
      label: `mathlibable:${d.base}`,
      phase: 'Assess',
      schema: SCHEMA,
      agentType: 'general-purpose',
    })
  ))
  results.push(...out.filter(Boolean))
  log(`${results.length}/${WL.length} assessed`)
}
return results
'''

JS = JS.replace('%PROJECT%', json.dumps(PROJ))
JS = JS.replace('%REFS%', json.dumps(REFS))
JS = JS.replace('%WL%', WL_LITERAL)
open(OUT, 'w').write(JS)
print(f"wrote {OUT} with {len(batch)} decls embedded")
