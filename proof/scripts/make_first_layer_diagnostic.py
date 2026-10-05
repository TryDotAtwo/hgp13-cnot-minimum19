"""Derive a bounded state exporter from the pinned verifier source.

Only the first successor layer is produced. The generated C++ is a diagnostic
instrument, never a replacement for the original full-run certificate.
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
    if len(sys.argv) != 2:
        raise SystemExit("usage: python make_first_layer_diagnostic.py OUTPUT.cpp")
    raw = SOURCE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != PINNED:
        raise ValueError("verifier source hash changed")
    source = '#include <sstream>\n' + raw.decode("utf-8")
    source = replace_once(source, "Result compute(const Case& c,const Catalogues& catalog) {",
                          "static int diag_case_index = -1;\n"
                          "Result compute(const Case& c,const Catalogues& catalog) {")
    source = replace_once(source, "        current.swap(next);",
                          "        current.swap(next);\n"
                          "        if (depth == 0 && diag_case_index >= 0) {\n"
                          "            for (const State& z : current) {\n"
                          "                std::cout << \"STATE \" << diag_case_index << ' ';\n"
                          "                for (int i=0;i<nc;i++) std::cout << z.row[i] << ',';\n"
                          "                std::cout << '|';\n"
                          "                for (auto w:z.appeared) std::cout << w << ',';\n"
                          "                std::cout << '|' << int(z.changed) << ','\n"
                          "                          << int(z.returned) << ',' << int(z.copied)\n"
                          "                          << ',' << int(z.extra) << '\\n';\n"
                          "            }\n"
                          "            break;\n"
                          "        }")
    source = replace_once(source, "int main(int argc,char** argv) {",
                          "int original_main_unused(int argc,char** argv) {")
    source += """
int main() {
    foundations();
    const std::array<Catalogues,2> catalog =
        {generate_catalogues(0),generate_catalogues(1)};
    const auto cases = make_cases();
    for (std::size_t i=0;i<cases.size();i++) {
        diag_case_index = int(i);
        compute(cases[i],catalog[cases[i].orientation]);
    }
    std::cout << "DIAGNOSTIC_FIRST_LAYER_ONLY " << cases.size() << '\\n';
}
"""
    path = Path(sys.argv[1])
    path.write_text(source, encoding="utf-8", newline="\n")
    print(hashlib.sha256(path.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
