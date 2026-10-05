"""Generate an untrusted graph candidate whose edge equalities Lean must check."""
import importlib.util
import json
import hashlib
from pathlib import Path

here = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("replay234", here / "replay_pilot234.py")
replay = importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)
layers = {d: sorted(xs) for d, xs in replay.layers.items()}
edges = {}
for d, states in layers.items():
    for s in states:
        edges[d, s] = [z for t in range(4) for j in range(8)
                       if (z := replay.move(d, s, t, j)) is not None]
        assert set(edges[d, s]) <= set(layers.get(d + 1, []))
report = json.loads((here / "pilot234_replay_report.json").read_text())
keys = [(item["depth"], item["history"]) for item in report["terminal_costs"]]
assert len(keys) == 16
ids = {(d, s): f"s{d}_{i}" for d in layers for i, s in enumerate(layers[d])}

def tree(xs):
    if not xs:
        return ".nil"
    mid = len(xs) // 2
    return f"(.node {tree(xs[:mid])} {xs[mid]} {tree(xs[mid + 1:])})"

def tree_def(name, xs):
    if len(xs) <= 512:
        return f"def {name} : Tree := {tree(xs)}\n"
    mid = len(xs) // 2
    return (tree_def(name + "_l", xs[:mid]) +
            tree_def(name + "_r", xs[mid + 1:]) +
            f"def {name} : Tree := .node {name}_l {xs[mid]} {name}_r\n")

out = ["""import SharedSearch
namespace HGP13.SectorGraph234
open SharedSearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/- The generated graph is checked against SharedSearch.next, not trusted.
   Full-word correspondence and catalogue completeness remain open. -/
inductive Tree where
  | nil
  | node : Tree → Nat → Tree → Tree
def lookup : Tree → Nat → Bool
  | .nil, _ => false
  | .node l a r, x => if x == a then true else if x < a then lookup l x else lookup r x
"""]
for k in (3, 4):
    out.append(tree_def(f"prefix{k}", sorted(replay.prefix[k])))
out.append("""def config : Config := ⟨[0,2], [3], [21,62,104,17,50,96,67],
  fun k x => lookup (if k ≤ 3 then prefix3 else prefix4) x⟩
""")
out.append("def keys : List (Nat × Nat) := [" +
           ", ".join(f"({d},{h})" for d, h in keys) + "]\n")
out.append("""def Covered (d : Nat) (s : State) : Prop :=
  terminal config s = true → (d,s.history) ∈ keys
instance (d : Nat) (s : State) : Decidable (Covered d s) := by
  unfold Covered
  infer_instance
def Safe : Nat → Nat → State → Prop
  | 0, d, s => Covered d s
  | k+1, d, s => Covered d s ∧ ∀ z ∈ next config d s, Safe k (d+1) z
theorem safe_succ (k d : Nat) (s : State) (zs : List State)
    (ht : Covered d s) (he : next config d s = zs)
    (hs : ∀ z ∈ zs, Safe k (d+1) z) : Safe (k+1) d s := by
  exact ⟨ht, fun z hz => hs z (he ▸ hz)⟩
inductive Reach : Nat → State → Nat → State → Prop where
  | refl (d s) : Reach d s 0 s
  | step {d s t k z} : t ∈ next config d s → Reach (d+1) t k z → Reach d s (k+1) z
theorem safe_reach {d s k z} (h : Reach d s k z) :
    ∀ fuel, k ≤ fuel → Safe fuel d s → Covered (d+k) z := by
  induction h with
  | refl d s =>
    intro fuel _ hs
    cases fuel with
    | zero => exact hs
    | succ n => exact hs.1
  | @step d s t k z ht hr ih =>
    intro fuel hk hs
    cases fuel with
    | zero => omega
    | succ n =>
      have h := ih n (by omega) (hs.2 _ ht)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
""")
for d in sorted(layers, reverse=True):
    for s in layers[d]:
        name = ids[d, s]
        children = [ids[d + 1, z] for z in edges[d, s]]
        childlist = "[" + ", ".join(children) + "]"
        literal = "⟨[" + ",".join(map(str, s[:4])) + "], " + ", ".join(map(str, s[4:])) + "⟩"
        out += [f"def {name} : State := {literal}\n",
                f"theorem {name}_edges : next config {d} {name} = {childlist} := by decide\n",
                f"theorem {name}_safe : Safe {13-d} {d} {name} := by\n",
                f"  apply safe_succ {12-d} {d} {name} {childlist} (by decide) {name}_edges\n"]
        if not children:
            out.append("  simp\n")
        else:
            out += ["  intro z hz\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz\n",
                    "  rcases hz with " + " | ".join("h" for _ in children) + "\n"]
            out += [f"  · subst z; exact {child}_safe\n" for child in children]
out += ["theorem initial_eq : initial config = s0_0 := by decide\n",
        "theorem initial_safe : Safe 13 0 (initial config) := by rw [initial_eq]; exact s0_0_safe\n",
        """theorem reachable_terminal_key {k z} (h : Reach 0 (initial config) k z) (hk : k ≤ 13)
    (ht : terminal config z = true) : (k,z.history) ∈ keys := by
  have hc := safe_reach h 13 hk initial_safe
  simpa using hc ht
end HGP13.SectorGraph234
"""]
path = here / "Graph234.lean"
path.write_text("".join(out), encoding="utf-8")
graph_report = {
    "candidate_only": True,
    "state_count": sum(map(len, layers.values())),
    "edge_count": sum(map(len, edges.values())),
    "terminal_key_count": len(keys),
    "graph_sha256": hashlib.sha256((here / "pilot234_graph.txt").read_bytes()).hexdigest(),
}
(here / "graph234_report.json").write_text(json.dumps(graph_report, indent=2) + "\n", encoding="utf-8")
print(f"Generated {sum(map(len,layers.values()))} states, {sum(map(len,edges.values()))} edges; {path.stat().st_size} bytes")
