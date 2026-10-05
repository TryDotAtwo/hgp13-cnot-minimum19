"""Independent Python replay of the exported sector-234 candidate graph.

The exact 8-bit form history is retained. This is a data audit, not Lean proof.
"""
import json
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
lines = (HERE / "pilot234_graph.txt").read_text(encoding="utf-8").splitlines()
prefix = {k: {int(s.split()[1]) for s in lines if s.startswith(f"PREFIX{k} ")}
          for k in (3, 4)}
layers = defaultdict(set)
for line in lines:
    if not line.startswith("STATE "):
        continue
    v = list(map(int, line.split()[1:]))
    depth = v[0]
    assert v[5] == 0
    hist = sum(v[6+i] << (64*i) for i in range(8))
    assert hist.bit_length() <= 256
    state = tuple(v[1:5]) + (hist,) + tuple(v[14:18])
    assert state not in layers[depth]
    layers[depth].add(state)

sources = (0, 2)
relays = (3,)
goals = (21, 62, 104, 17, 50, 96, 67)
want = (1, 4, 67, 128 ^ 17)
fixed = (2, 8, 16, 32)
passive = (21, 62, 104, 50, 96)
base = {0, 1, 2, 4, 8, 16, 32, 64}

def has(hist, value):
    return (hist >> value) & 1

def projected(hist):
    return (hist | (hist >> 128)) & ((1 << 128)-1)

def encode(values):
    answer = 0
    for value in sorted(values):
        answer = answer * 128 + value
    return answer

def move(depth, state, t, j):
    if t == j:
        return None
    rows = list(state[:4])
    hist, changed, returned, copied, extra = state[4:]
    value = rows[t] ^ ((rows + list(fixed))[j])
    if value == 0:
        return None
    p = value & 127
    ret = t < 2 and value == (1 << sources[t]) and (changed >> t & 1) and not (returned >> t & 1)
    copy = t > 2 and (rows[t] & 127) == 0 and p != 0 and not (copied >> (t-3) & 1)
    if t < 2:
        changed |= 1 << t
    if ret:
        returned |= 1 << t
    if copy:
        copied |= 1 << (t-3)
    old = projected(hist)
    seen = p in base or has(old, p)
    extra += int(bool(seen and not (ret or copy)))
    if extra > 0:
        return None
    aux = [a for a in range(1,128) if has(old,a) and a not in base and a not in goals]
    if not seen and p not in goals:
        aux.append(p)
    capacity = 3
    if len(aux) > capacity or encode(aux) not in prefix[capacity]:
        return None
    rows[t] = value
    hist |= 1 << value
    known = projected(hist)
    for i in range(2,4):
        f = want[i] & 127
        if has(known,f) and rows[i] != want[i] and (i == 2 or (rows[i] & 127) != 0 or f not in rows):
            return None
    if any(has(known,f) and not has(hist,f) for f in passive):
        return None
    delta = [rows[i] ^ want[i] for i in range(4) if rows[i] != want[i]]
    available = set(rows + list(want) + list(fixed))
    missing = {d for d in delta if d not in available}
    untouched = sum(1 for i in range(2) if not (changed >> i & 1))
    bound = max(len(delta) + 2*untouched, len(delta) + (len(missing)+1)//2)
    if depth + 1 + bound > 13:
        return None
    return tuple(rows) + (hist, changed, returned, copied, extra)

def cost(hist):
    distances = [999]*256
    distances[0] = 0
    for v in range(1,256):
        if not has(hist,v):
            continue
        for x in range(256):
            y = x ^ v
            if x < y:
                a,b = distances[x],distances[y]
                distances[x],distances[y] = min(a,b+1),min(b,a+1)
    return distances

assert layers[0] == {(1,4,64,128,sum(1 << (1 << i) for i in range(8)),0,0,0,0)}
terminal_costs = []
for depth in sorted(layers):
    successors = set()
    for state in layers[depth]:
        if state[:4] == want and state[5] == 3:
            distances = cost(state[4])
            terminal_costs.append((depth, depth + sum(distances[f] for f in passive), state[4]))
        if depth < 13:
            successors.update(z for t in range(4) for j in range(8)
                              if (z := move(depth,state,t,j)) is not None)
    assert successors == layers.get(depth+1,set()), (depth,len(successors),len(layers.get(depth+1,set())))

assert len(terminal_costs) == 16
assert min(x[1] for x in terminal_costs) == 21
report = {
    "status": "Python/C++ graph agreement; Lean certificate still open",
    "layers": {str(d):len(layers[d]) for d in sorted(layers)},
    "terminals": len(terminal_costs),
    "minimum_terminal_total_cost": min(x[1] for x in terminal_costs),
    "terminal_costs": sorted([{"depth":d,"total_cost":c,"history":h}
                              for d,c,h in terminal_costs], key=lambda x:(x["depth"],x["history"])),
}
(HERE / "pilot234_replay_report.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
print(json.dumps({k:v for k,v in report.items() if k != "terminal_costs"},indent=2))
