// Independent exhaustive catalogue enumerator. It does not include the verifier.
// The closure step adds every currently derivable pending form simultaneously.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <vector>

using Keys = std::set<std::uint32_t>;
static constexpr std::array<std::array<int,7>,2> goals{{
    {{73,82,3,6,27,54,100}}, {{21,62,104,17,50,96,67}}
}};

bool feasible(const std::array<int,7>& goal, const std::vector<int>& chosen) {
    std::array<bool,128> present{};
    std::vector<int> available;
    for (int i=0;i<7;++i) {
        int x=1<<i;
        present[x]=true;
        available.push_back(x);
    }
    std::vector<int> pending(goal.begin(),goal.end());
    pending.insert(pending.end(),chosen.begin(),chosen.end());
    for (;;) {
        bool all=true;
        for (int x:pending) if (!present[x]) { all=false; break; }
        if (all) return true;
        std::array<bool,128> possible{};
        for (int a:available) for (int b:available) possible[a^b]=true;
        std::vector<int> additions;
        for (int x:pending) if (!present[x] && possible[x]) additions.push_back(x);
        if (additions.empty()) return false;
        for (int x:additions) { present[x]=true; available.push_back(x); }
    }
}

std::uint32_t key(const std::vector<int>& chosen, unsigned bits) {
    std::uint32_t answer=0;
    for (std::size_t i=0;i<chosen.size();++i)
        if (bits & (1u<<i)) answer=answer*128u+unsigned(chosen[i]);
    return answer;
}

void insert_subsets(Keys& out, const std::vector<int>& chosen) {
    for (unsigned bits=0;bits<(1u<<chosen.size());++bits)
        out.insert(key(chosen,bits));
}

int main() {
    for (int orientation=0;orientation<2;++orientation) {
        std::array<bool,128> excluded{};
        excluded[0]=true;
        for (int i=0;i<7;++i) excluded[1<<i]=true;
        for (int x:goals[orientation]) excluded[x]=true;
        std::vector<int> options;
        for (int x=1;x<128;++x) if (!excluded[x]) options.push_back(x);
        if (options.size()!=113) throw std::runtime_error("auxiliary domain");
        Keys prefix3,prefix4;
        std::uint64_t count3=0,count4=0;
        for (std::size_t i=0;i<options.size();++i)
        for (std::size_t j=i+1;j<options.size();++j)
        for (std::size_t k=j+1;k<options.size();++k) {
            std::vector<int> chosen{options[i],options[j],options[k]};
            if (feasible(goals[orientation],chosen)) {
                ++count3;
                insert_subsets(prefix3,chosen);
            }
            for (std::size_t l=k+1;l<options.size();++l) {
                chosen.push_back(options[l]);
                if (feasible(goals[orientation],chosen)) {
                    ++count4;
                    insert_subsets(prefix4,chosen);
                }
                chosen.pop_back();
            }
        }
        prefix4.insert(prefix3.begin(),prefix3.end());
        std::cerr << "COUNTS " << orientation << ' ' << count3 << ' ' << count4
                  << ' ' << prefix3.size() << ' ' << prefix4.size() << '\n';
        for (std::uint32_t x:prefix3) std::cout << orientation << " 3 " << x << '\n';
        for (std::uint32_t x:prefix4) std::cout << orientation << " 4 " << x << '\n';
    }
}
