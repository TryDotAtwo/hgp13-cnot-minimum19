"""Export dual cost potentials; untrusted candidate data for a future Lean check."""
import hashlib
import json
from collections import deque
from pathlib import Path

p = Path(__file__).parent
source = p / 'exported359.txt'
goals = [21, 62, 104, 17, 50, 96]
terminals = []
for line in source.read_text().splitlines():
    if not line.startswith('STATE '):
        continue
    v = list(map(int, line.split()[1:]))
    depth, rows, changed = v[0], v[1:6], v[14]
    # Case 359: transpose, active source [2], no carriers.
    if rows[:2] != [4, 67] or changed != 1:
        continue
    history = sum(v[6+i] << (64*i) for i in range(8))
    assert history >> 128 == 0
    available = [x for x in range(128) if (history >> x) & 1]
    distance = [999] * 128
    distance[0] = 0
    queue = deque([0])
    while queue:
        x = queue.popleft()
        for a in available:
            y = x ^ a
            if distance[y] > distance[x] + 1:
                distance[y] = distance[x] + 1
                queue.append(y)
    assert all(distance[x ^ a] <= distance[x] + 1 for x in range(128) for a in available)
    lower = depth + sum(distance[g] for g in goals)
    assert lower > 18
    terminals.append(dict(depth=depth, history=history, available=available,
                          potential=distance, total_lower_bound=lower))
assert len(terminals) == 36
result = dict(scope='Untrusted candidate potentials; not a Lean terminal certificate',
              source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
              sector=359, terminal_count=len(terminals),
              minimum_lower_bound=min(t['total_lower_bound'] for t in terminals),
              terminals=terminals)
(p / 'potential359.json').write_text(json.dumps(result, indent=2))
print('Candidate potentials:', len(terminals), 'terminals; minimum bound', result['minimum_lower_bound'])
