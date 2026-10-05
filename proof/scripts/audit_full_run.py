"""Fail-closed structural audit of the preserved HGP13 C++ run transcript.

This checks the transcript and accompanying source/summary as data. It does
not prove that this source produced the transcript or that C++ implements the
Lean abstract search. Run from any directory with Python 3.11+.
"""
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "hgp13_verify.cpp"
LOG = ROOT / "verification_run.txt"
SUMMARY = ROOT / "verification_summary.json"
OUT = ROOT / "evidence" / "full_run_audit.json"
PINNED_SOURCE = "2174f445df534455c30e9ae7b54b8dfff4fdbdce3ff4eaf6b7d7e557fa3f8e4c"
PINNED_SECTOR_SEQUENCE = "ae5942bfa77d4a416a843cce5d5478b3fcedff7be896e9dbcaa71b4b9fac334d"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def expected_cases():
    cases = []
    for a in range(6):
        for b in range(a + 1, 6):
            for c in range(6):
                for d in range(c + 1, 6):
                    cases.append((0, 0, 2, 2))
    for a in range(6):
        for b in range(a + 1, 6):
            for c in range(6):
                cases.append((1, 1, 2, 1))
    for a in range(6):
        for b in range(6):
            cases.append((0, 2, 1, 1))
    for orientation in range(2):
        for a in range(6):
            cases.append((orientation, 3, 1, 0))
    require(len(cases) == 363, "case enumeration changed")
    return cases


def parse_run(path):
    lines = path.read_text(encoding="utf-8").splitlines()
    require(lines[:2] == ["CATALOGUES 298 21687 298 21823", "FOUNDATIONS_OK"],
            f"unexpected header: {path}")
    require(lines[-2:] == ["COMPLETED 363 TOTAL_LABELS 306922994",
                           "VERIFIED_FIXED_MATRIX_MINIMUM_19"],
            f"unexpected trailer: {path}")
    cases = {}
    families = {}
    expect = expected_cases()
    for line in lines[2:-2]:
        if line.startswith("CASE "):
            row = json.loads(line[5:])
            require(set(row) == {"id", "orientation", "family", "layers", "total",
                                 "terminals", "best", "status"}, "unexpected case fields")
            case_id = row["id"]
            require(type(case_id) is int and 0 <= case_id < 363 and case_id not in cases,
                    "duplicate or invalid case ID")
            orientation, family, ns, ny = expect[case_id]
            require((row["orientation"], row["family"]) == (orientation, family),
                    f"case {case_id}: orientation/family mismatch")
            layers = row["layers"]
            require(isinstance(layers, list) and 1 <= len(layers) <= 13 + ny,
                    f"case {case_id}: invalid depth count")
            require(all(type(x) is int and x >= 0 for x in layers) and layers[0] == 1,
                    f"case {case_id}: invalid layers")
            require(sum(layers) == row["total"] and row["total"] > 0,
                    f"case {case_id}: total mismatch")
            require(type(row["terminals"]) is int and
                    0 <= row["terminals"] <= row["total"],
                    f"case {case_id}: invalid terminals")
            require(type(row["best"]) is int and row["best"] > 18 and
                    row["status"] == "zero_support", f"case {case_id}: cheap candidate")
            require((row["terminals"] == 0) == (row["best"] == 999),
                    f"case {case_id}: best/terminal inconsistency")
            cases[case_id] = row
        elif line.startswith("FAMILY "):
            match = re.fullmatch(
                r"FAMILY (\d+) CASES (\d+) LABELS (\d+) MAX_LAYER (\d+) TERMINALS (\d+)",
                line)
            require(match is not None, "malformed family summary")
            f, count, labels, maximum, terminals = map(int, match.groups())
            require(0 <= f <= 3 and f not in families, "duplicate family summary")
            families[f] = (count, labels, maximum, terminals)
        else:
            raise ValueError(f"unexpected log line: {line[:100]}")
    require(sorted(cases) == list(range(363)), "case coverage incomplete")
    require(sorted(families) == list(range(4)), "family coverage incomplete")
    for f in range(4):
        rows = [row for row in cases.values() if row["family"] == f]
        actual = (len(rows), sum(row["total"] for row in rows),
                  max(max(row["layers"]) for row in rows),
                  sum(row["terminals"] for row in rows))
        require(actual == families[f], f"family {f} aggregate mismatch")
    require(sum(row["total"] for row in cases.values()) == 306922994,
            "overall label count mismatch")
    return cases, families


def read_lean_tree_keys(path, root):
    """Parse the emitted literal Tree syntax, including shared subtree refs."""
    definitions = {}
    pattern = re.compile(r"^def (prefix[34](?:_[lr])*) : Tree := (.+)$", re.M)
    token_pattern = re.compile(r"\(|\)|\.node|\.nil|[A-Za-z_][A-Za-z_0-9]*|\d+")
    for name, expression in pattern.findall(path.read_text(encoding="utf-8")):
        tokens = []
        position = 0
        for match in token_pattern.finditer(expression):
            require(not expression[position:match.start()].strip(),
                    f"unparsed Tree syntax in {name}")
            tokens.append(match.group())
            position = match.end()
        require(not expression[position:].strip(), f"trailing Tree syntax in {name}")
        index = 0

        def parse():
            nonlocal index
            require(index < len(tokens), f"truncated Tree expression in {name}")
            token = tokens[index]
            index += 1
            if token == "(":
                result = parse()
                require(index < len(tokens) and tokens[index] == ")",
                        f"unclosed Tree expression in {name}")
                index += 1
                return result
            if token == ".nil":
                return None
            if token == ".node":
                left = parse()
                require(index < len(tokens) and tokens[index].isdigit(),
                        f"missing Tree key in {name}")
                key = int(tokens[index])
                index += 1
                right = parse()
                return (left, key, right)
            require(token in definitions, f"unknown Tree reference {token}")
            return definitions[token]

        definitions[name] = parse()
        require(index == len(tokens), f"extra Tree tokens in {name}")
    require(root in definitions, f"missing {root} in {path}")

    def inorder(tree):
        if tree is None:
            return []
        left, key, right = tree
        return inorder(left) + [key] + inorder(right)

    keys = inorder(definitions[root])
    require(keys == sorted(set(keys)), f"invalid BST ordering in {path}:{root}")
    return keys


def audit_literal_tables():
    exported = {(orientation, capacity): [] for orientation in range(2)
                for capacity in (3, 4)}
    for line in (ROOT / "scale_pilot" / "catalogue_keys.txt").read_text(
            encoding="utf-8").splitlines():
        orientation, capacity, key = map(int, line.split())
        require((orientation, capacity) in exported, "invalid exported key group")
        exported[orientation, capacity].append(key)
    paths = {0: ROOT / "lean" / "OriginalPrefixesLite.lean",
             1: ROOT / "lean" / "SectorGraph359.lean"}
    counts = {}
    for orientation, path in paths.items():
        for capacity in (3, 4):
            keys = exported[orientation, capacity]
            require(keys == sorted(set(keys)), "exported keys not sorted/unique")
            literal = read_lean_tree_keys(path, f"prefix{capacity}")
            require(literal == keys,
                    f"literal table differs from exported key set: {orientation}/{capacity}")
            counts[f"{orientation}/{capacity}"] = len(keys)
    return counts


def main():
    source_hash = sha256(SOURCE)
    require(source_hash == PINNED_SOURCE, "source hash mismatch")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    require(summary["source_sha256"] == source_hash and
            summary["case_count"] == 363 and
            summary["total_labels"] == 306922994 and
            summary["all_cases_zero_support"] is True,
            "summary disagrees with pinned source or counts")
    cases, families = parse_run(LOG)
    ubsan_path = ROOT / "evidence" / "ubsan_case357.txt"
    ubsan_lines = ubsan_path.read_text(encoding="utf-8").splitlines()
    require(ubsan_lines[0:2] == ["CATALOGUES 298 21687 298 21823", "FOUNDATIONS_OK"]
            and ubsan_lines[-1:] == ["PARTIAL_CHECK_ONLY"] and len(ubsan_lines) == 4,
            "malformed UBSan diagnostic transcript")
    require(ubsan_lines[2].startswith("CASE ") and
            json.loads(ubsan_lines[2][5:]) == cases[357],
            "UBSan diagnostic differs from full case 357")
    first_layers_path = ROOT / "evidence" / "lean_first_layers.txt"
    first_layers = [tuple(map(int, line.split())) for line in
                    first_layers_path.read_text(encoding="utf-8").splitlines()]
    require(len(first_layers) == 363 and
            [case_id for case_id, _ in first_layers] == list(range(363)),
            "Lean first-layer export has missing or duplicate sector IDs")
    require(all(len(cases[i]["layers"]) > 1 and n == cases[i]["layers"][1]
                for i, n in first_layers),
            "Lean first-layer sizes disagree with C++ transcript")
    first_state_paths = {name: ROOT / "evidence" / f"{name}_first_layer_states.txt"
                         for name in ("cpp", "lean")}
    first_state_counts = {}
    for name, path in first_state_paths.items():
        lines = path.read_text(encoding="utf-8").splitlines()
        require(lines[-1:] == ["DIAGNOSTIC_FIRST_LAYER_ONLY 363"],
                f"{name} first-state diagnostic marker missing")
        states = Counter(lines[:-1])
        require(len(states) == len(lines)-1 == sum(n for _, n in first_layers)
                and all(n == 1 for n in states.values()),
                f"{name} first-state export has duplicate or missing states")
        counts = Counter()
        for line in states:
            match = re.fullmatch(r"STATE (\d+) ([0-9,|]+)", line)
            require(match is not None, f"malformed {name} state line")
            counts[int(match.group(1))] += 1
        require(all(counts[i] == n for i, n in first_layers),
                f"{name} state counts disagree with first-layer counts")
        first_state_counts[name] = states
    require(first_state_counts["cpp"] == first_state_counts["lean"],
            "C++ and Lean first-layer state sets differ")
    cpp_cases = ROOT / "evidence" / "cpp_sector_cases.txt"
    lean_cases = ROOT / "evidence" / "lean_sector_cases.txt"
    cpp_case_lines = cpp_cases.read_text(encoding="utf-8").splitlines()
    lean_case_lines = lean_cases.read_text(encoding="utf-8").splitlines()
    require(len(cpp_case_lines) == 363 and cpp_cases.read_bytes() == lean_cases.read_bytes()
            and cpp_case_lines == lean_case_lines and
            sha256(cpp_cases) == PINNED_SECTOR_SEQUENCE,
            "C++ and Lean concrete sector sequences differ")
    literal_key_counts = audit_literal_tables()
    comparisons = {}
    for name in ("independent_run.txt", "supplied_run.txt"):
        path = ROOT / "evidence" / name
        other, _ = parse_run(path)
        require(other == cases, f"case records differ in {name}")
        comparisons[name] = {"sha256": sha256(path), "case_records_equal": True}
    report = {
        "scope": "transcript structure and saved-case agreement only",
        "source_sha256": source_hash,
        "log_sha256": sha256(LOG),
        "summary_sha256": sha256(SUMMARY),
        "cases": len(cases),
        "families": {str(k): {"cases": v[0], "labels": v[1],
                              "max_layer": v[2], "terminals": v[3]}
                     for k, v in families.items()},
        "total_labels": 306922994,
        "total_terminals": sum(row["terminals"] for row in cases.values()),
        "best_by_family": {str(f): min(row["best"] for row in cases.values()
                                        if row["family"] == f) for f in range(4)},
        "comparison_logs": comparisons,
        "literal_table_key_counts": literal_key_counts,
        "literal_tables_equal_saved_cpp_key_export": True,
        "sector_sequence": {"count": len(cpp_case_lines), "cpp_sha256": sha256(cpp_cases),
                            "lean_sha256": sha256(lean_cases), "byte_equal":
                            cpp_cases.read_bytes() == lean_cases.read_bytes()},
        "first_layer_comparison": {"cases": len(first_layers),
                                   "lean_export_sha256": sha256(first_layers_path),
                                   "all_sizes_equal_cpp_log": True},
        "first_layer_state_comparison": {
            "states": len(first_state_counts["cpp"]), "all_363_state_sets_equal": True,
            "cpp_sha256": sha256(first_state_paths["cpp"]),
            "lean_sha256": sha256(first_state_paths["lean"]),
            "scope": "one transition only; later layers not compared"},
        "ubsan_case357": {"transcript_sha256": sha256(ubsan_path),
                          "case_record_equal_full_log": True,
                          "all_cases_sanitized": False},
        "log_cryptographically_attests_compiler_or_executed_source": False,
        "cpp_refines_lean_proved_by_this_audit": False,
        "finite_facts_lean_kernel_checked_by_this_audit": False,
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(cases)} cases; {report['total_labels']} labels; "
          f"{report['total_terminals']} terminals; external trust boundary open")


if __name__ == "__main__":
    main()
