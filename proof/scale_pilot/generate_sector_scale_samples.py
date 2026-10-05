"""Export bounded representative full-history states and their exact successor lists.

This instruments the pinned C++ search only for performance probes.  Its output
is candidate data; no mathematical assertion is accepted from the exporter.
"""
from pathlib import Path

here = Path(__file__).resolve().parent
package_source = here.parent / "hgp13_verify.cpp"
source_path = package_source if package_source.exists() else here.parent / "outputs/hgp13-arxiv/hgp13_verify.cpp"
src = source_path.read_text(encoding="utf-8")

needle = "        result.layers.push_back(current.size());"
assert src.count(needle) == 1
src = src.replace(needle, """        const State* diagnostic = nullptr;
        if (depth == 4 || depth == 8 || depth == 11) {
            auto score = [](const State& s) {
                int n=0;
                for (U64 x : s.appeared) n += __builtin_popcountll(x);
                return n;
            };
            for (const State& s : current)
                if (!diagnostic || score(s) > score(*diagnostic) ||
                    (score(s) == score(*diagnostic) &&
                     std::tie(s.row,s.appeared,s.changed,s.returned,s.copied,s.extra) <
                     std::tie(diagnostic->row,diagnostic->appeared,
                              diagnostic->changed,diagnostic->returned,
                              diagnostic->copied,diagnostic->extra)))
                    diagnostic = &s;
            if (diagnostic) {
                std::cout << "SAMPLE " << depth << " " << score(*diagnostic)
                          << " " << ns << " " << ny;
                for (int i=0;i<nc;i++) std::cout << " " << diagnostic->row[i];
                for (U64 x : diagnostic->appeared) std::cout << " " << x;
                std::cout << " " << int(diagnostic->changed)
                          << " " << int(diagnostic->returned)
                          << " " << int(diagnostic->copied)
                          << " " << int(diagnostic->extra) << "\\n";
            }
        }
        result.layers.push_back(current.size());""")

needle = "                next.insert(nextstate);"
assert src.count(needle) == 1
src = src.replace(needle, """                if (diagnostic == &s) {
                    std::cout << "EDGE " << depth << " " << t << " " << j;
                    for (int i=0;i<nc;i++) std::cout << " " << nextstate.row[i];
                    for (U64 x : nextstate.appeared) std::cout << " " << x;
                    std::cout << " " << int(nextstate.changed)
                              << " " << int(nextstate.returned)
                              << " " << int(nextstate.copied)
                              << " " << int(nextstate.extra) << "\\n";
                }
                next.insert(nextstate);""")
needle = "    Result result;"
assert src.count(needle) == 1
src = src.replace(needle, needle + "\n    State beststate;\n    int bestdepth=-1;")
needle = "            result.best=std::min(result.best,length);"
assert src.count(needle) == 1
src = src.replace(needle, """            if (length < result.best) {
                result.best=length;
                beststate=s;
                bestdepth=depth;
            }""")
needle = "    return result;\n}\n\nvoid foundations()"
assert src.count(needle) == 1
src = src.replace(needle, """    if (bestdepth>=0) {
        std::cout << "TERMINAL " << bestdepth << " " << result.best
                  << " " << ns << " " << ny;
        for (int i=0;i<nc;i++) std::cout << " " << beststate.row[i];
        for (U64 x : beststate.appeared) std::cout << " " << x;
        std::cout << " " << int(beststate.changed)
                  << " " << int(beststate.returned)
                  << " " << int(beststate.copied)
                  << " " << int(beststate.extra) << "\\n";
    }
    return result;
}

void foundations()""")
src = src.replace("#include <mutex>", "#include <mutex>\n#include <tuple>")
(here / "sector_scale_samples.cpp").write_text(src, encoding="utf-8")
print(here / "sector_scale_samples.cpp")
