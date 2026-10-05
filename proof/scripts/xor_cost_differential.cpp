// Bounded independent differential test of the pinned xor_cost routine.
// The oracle is shortest-path BFS over XOR generators, not its pairwise DP.
#include <queue>
#define main verifier_main_unused
#include "../hgp13_verify.cpp"
#undef main

static std::vector<int> oracle(const std::vector<int>& forms, int dim) {
    const int size=1<<dim;
    std::vector<int> distance(size,999);
    std::queue<int> queue;
    distance[0]=0;
    queue.push(0);
    while (!queue.empty()) {
        int x=queue.front();
        queue.pop();
        for (int v:forms) {
            int y=x^v;
            if (distance[y]>distance[x]+1) {
                distance[y]=distance[x]+1;
                queue.push(y);
            }
        }
    }
    return distance;
}

int main() {
    std::uint64_t seed=0xdecafbad637a59e1ULL;
    std::uint64_t trials=0,checked=0;
    auto next_random=[&]() {
        seed^=seed<<13;
        seed^=seed>>7;
        seed^=seed<<17;
        return seed;
    };
    for (int dim=7;dim<=9;++dim) {
        const int size=1<<dim;
        for (int scenario=0;scenario<506;++scenario) {
            State s;
            std::vector<int> forms;
            for (int v=1;v<size;++v) {
                bool include=false;
                if (scenario==1) include=(v==1);
                else if (scenario==2) include=((v&(v-1))==0);
                else if (scenario==3) include=true;
                else if (scenario==4) include=(v==size-1);
                else if (scenario==5) include=(v==size/2);
                else if (scenario>=6) include=((next_random()&15u)==0);
                if (include) { remember(s,v); forms.push_back(v); }
            }
            const auto actual=xor_cost(s,dim);
            const auto expected=oracle(forms,dim);
            if (actual!=expected) {
                std::cerr << "MISMATCH dimension=" << dim
                          << " scenario=" << scenario << '\n';
                return 1;
            }
            ++trials;
            checked+=size;
        }
    }
    std::cout << "PASS XOR_COST_DIFFERENTIAL trials=" << trials
              << " cells=" << checked << " seed=decafbad637a59e1\n";
}
