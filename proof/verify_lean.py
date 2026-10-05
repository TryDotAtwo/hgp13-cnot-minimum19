"""Build pinned Lean sources and bind a complete axiom audit to their hashes.

This verifies the partial development listed in STATUS.md, not NoShortProgram.
Requires the existing local/lean4:4.34.0 Docker image; never pulls an image.
"""
import hashlib
import json
import re
import subprocess
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LEAN = ROOT / 'lean'
OUT = ROOT / 'evidence'
OUT.mkdir(exist_ok=True)
IMAGE = 'local/lean4:4.34.0'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def snapshot():
    result = {str(p.relative_to(ROOT)): digest(p) for p in
            sorted(LEAN.iterdir()) if p.suffix in ('.lean', '.toml', '.json')
            or p.name == 'lean-toolchain'}
    result['claim_map.json'] = digest(ROOT / 'claim_map.json')
    result['verify_lean.py'] = digest(Path(__file__))
    return result

def check_inventory(lean):
    """Fail closed when an accepted module or theorem is omitted from the gate."""
    modules = {p.stem for p in lean.glob('*.lean')}
    config = tomllib.loads((lean / 'lakefile.toml').read_text(encoding='utf-8'))
    roots = [r for lib in config.get('lean_lib', []) for r in lib.get('roots', [])]
    if set(roots) != modules or len(roots) != len(set(roots)):
        raise RuntimeError('Lake roots must include every accepted Lean module exactly once')
    audit = (lean / 'Audit.lean').read_text(encoding='utf-8')
    imports = re.findall(r'^import (\w+)\s*$', audit, re.M)
    if set(imports) != modules - {'Audit'} or len(imports) != len(set(imports)):
        raise RuntimeError('Audit imports must include every accepted proof module exactly once')
    expected = []
    for module in sorted(modules - {'Audit'}):
        source = (lean / (module + '.lean')).read_text(encoding='utf-8')
        if re.search(r'^\s*@\[', source, re.M):
            raise RuntimeError(f'Unsupported attributed declaration layout in {module}')
        namespaces = re.findall(r'^namespace (\S+)', source, re.M)
        if len(namespaces) != 1:
            raise RuntimeError(f'Unsupported namespace inventory in {module}')
        # This repository uses one namespace and unindented named theorems.
        # Refuse alternate declaration layouts rather than silently skipping them.
        names = re.findall(r'^theorem (\w+)', source, re.M)
        declarations = re.findall(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+', source, re.M)
        if len(names) != len(declarations):
            raise RuntimeError(f'Unsupported theorem declaration layout in {module}')
        expected.extend(namespaces[0] + '.' + name for name in names)
    requested = re.findall(r'^#print axioms ([\w.]+)', audit, re.M)
    if (set(expected) != set(requested) or len(requested) != len(set(requested))
            or len(expected) != len(set(expected))):
        raise RuntimeError('Axiom requests must cover every accepted named theorem exactly once')
    return dict(modules=sorted(modules), theorem_count=len(expected))

def run(argv, name):
    p = subprocess.run(argv, text=True, encoding='utf-8', errors='replace',
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / (name + '.log')).write_text(p.stdout, encoding='utf-8')
    if p.returncode:
        raise RuntimeError(f'{name} failed ({p.returncode}):\n{p.stdout}')
    return dict(argv=argv, exit_code=p.returncode, output=p.stdout)

for src in LEAN.glob('*.lean'):
    if re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b', src.read_text(), re.M):
        raise RuntimeError(f'Forbidden proof placeholder or native reduction: {src}')

inventory = check_inventory(LEAN)
before = snapshot()
identity = run(['docker', 'image', 'inspect', IMAGE, '--format', '{{.Id}}'], 'image')
image_id = identity['output'].strip()
base = ['docker', 'run', '--rm', '--network', 'none', '--mount',
        f'type=bind,source={LEAN},target=/work', '-w', '/work', image_id]
version = run(base + ['lean', '--version'], 'lean_version')
if 'version 4.34.0,' not in version['output']:
    raise RuntimeError('Unexpected Lean version')
build = run(base + ['lake', 'build'], 'build')
audit = run(base + ['lake', 'env', 'lean', 'Audit.lean'], 'axioms')

requested = re.findall(r'^#print axioms ([\w.]+)', (LEAN / 'Audit.lean').read_text(), re.M)
found = {}
for m in re.finditer(r"'([\w.]+)' depends on axioms: \[([^]]*)\]", audit['output']):
    found[m[1]] = [a.strip() for a in m[2].split(',') if a.strip()]
for z in re.finditer(r"'([\w.]+)' does not depend on any axioms", audit['output']):
    found[z[1]] = []
if set(requested) != set(found):
    raise RuntimeError(f'Incomplete axiom audit: {set(requested) - set(found)}')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
if any(set(axioms) - allowed for axioms in found.values()):
    raise RuntimeError('Disallowed transitive axiom')

claims = json.loads((ROOT / 'claim_map.json').read_text(encoding='utf-8'))['claims']
for claim in claims:
    if claim['status'] == 'kernel_verified':
        if not claim['declarations'] or set(claim['declarations']) - set(found):
            raise RuntimeError(f'Missing audited declarations for claim {claim["id"]}')
    for part in claim.get('partial_results', []):
        if part['status'] == 'kernel_verified':
            if not part['declarations'] or set(part['declarations']) - set(found):
                raise RuntimeError(f'Missing audited partial declarations for {claim["id"]}')
if next(c for c in claims if c['id'] == 'main.minimum19')['status'] != 'open':
    raise RuntimeError('Main theorem status needs a separate completed-proof gate')
after = snapshot()
if before != after:
    raise RuntimeError('Source/configuration changed during the audit')
record = dict(scope='Partial formalization only; NoShortProgram remains open',
              inventory=inventory,
              source_sha256=after, image_id=image_id, commands=[version,build,audit],
              declaration_axioms=found, no_short_program_proved=False)
record['claim_status'] = {c['id']: c['status'] for c in claims}
(OUT / 'lean_verification.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
print(f'PASS: {len(found)} declarations audited; NoShortProgram remains OPEN.')
