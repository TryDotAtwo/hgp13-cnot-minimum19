from pathlib import Path
p=Path(__file__).resolve().parent
root=p.parent if (p.parent/'hgp13_verify.cpp').exists() else p.parents[1]/'outputs/hgp13-arxiv'
s=(root/'hgp13_verify.cpp').read_text()
s=s.replace('result.layers.push_back(current.size());', '''result.layers.push_back(current.size());
        for (const State& st : current) {
            std::cout << "STATE " << depth;
            for (auto x:st.row) std::cout << " " << x;
            for (auto x:st.appeared) std::cout << " " << x;
            std::cout << " " << int(st.changed) << " " << int(st.returned)
                      << " " << int(st.copied) << " " << int(st.extra) << "\\n";
        }''')
s=s.replace('auto cases=make_cases();', '''for (auto x:catalog[1].prefix[0]) std::cout << "PREFIX " << x << "\\n";
        auto cases=make_cases();''')
(p/'export.cpp').write_text(s)
