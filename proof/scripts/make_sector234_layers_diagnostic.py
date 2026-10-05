"""Export all layers of checked sector 234 or 359 from a pinned verifier.

This diagnostic does not replace the pinned source or the preserved full run.
"""
import hashlib
import sys
from pathlib import Path

SOURCE = Path(__file__).resolve().parents[1] / "hgp13_verify.cpp"
PINNED = "2174f445df534455c30e9ae7b54b8dfff4fdbdce3ff4eaf6b7d7e557fa3f8e4c"


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError(f"expected one source insertion point: {old!r}")
    return source.replace(old, new)


def main():
    if len(sys.argv) not in (2, 3):
        raise SystemExit("usage: python make_sector234_layers_diagnostic.py OUTPUT.cpp [234|359]")
    case_id = int(sys.argv[2]) if len(sys.argv) == 3 else 234
    if case_id not in (234, 359):
        raise ValueError("only checked sectors 234 and 359 are supported")
    raw = SOURCE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != PINNED:
        raise ValueError("verifier source hash changed")
    source = raw.decode("utf-8")
    source = replace_once(
        source,
        "        result.layers.push_back(current.size());",
        "        result.layers.push_back(current.size());\n"
        "        for (const State& st : current) {\n"
        "            std::cout << \"STATE \" << depth;\n"
        "            for (auto x : st.row) std::cout << ' ' << x;\n"
        "            for (auto x : st.appeared) std::cout << ' ' << x;\n"
        "            std::cout << ' ' << int(st.changed) << ' ' << int(st.returned)\n"
        "                      << ' ' << int(st.copied) << ' ' << int(st.extra) << '\\n';\n"
        "        }",
    )
    source = replace_once(source, "int main(int argc,char** argv) {",
                          "int original_main_unused(int argc,char** argv) {")
    source += """
int main() {
    foundations();
    const std::array<Catalogues,2> catalog =
        {generate_catalogues(0),generate_catalogues(1)};
    const auto cases = make_cases();
    const int id = CASE_ID;
    const auto r = compute(cases[id],catalog[cases[id].orientation]);
    print_case(id,cases[id],r);
    std::cout << "DIAGNOSTIC_SECTOR_LAYERS_ONLY " << id << '\\n';
}
""".replace("CASE_ID", str(case_id))
    path = Path(sys.argv[1])
    path.write_text(source, encoding="utf-8", newline="\n")
    print(hashlib.sha256(path.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
