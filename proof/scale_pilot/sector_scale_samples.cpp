// Self-contained finite certificate for ONE fixed 13 by 13 binary matrix.
// Build: g++ -O3 -std=c++17 -pthread hgp13_verify.cpp -o hgp13_verify
// Full verification: ./hgp13_verify 3
// One diagnostic case only: ./hgp13_verify --one 0
// No input files, saved catalogues, libraries beyond C++17, or network access.
#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <exception>
#include <functional>
#include <iostream>
#include <mutex>
#include <tuple>
#include <set>
#include <stdexcept>
#include <string>
#include <thread>
#include <unordered_set>
#include <vector>

using U64 = std::uint64_t;
using Mask = std::array<U64,2>;
const std::array<int,13> TARGET =
    {1,2,4,8,16,32,329,402,292,515,1030,2075,4150};
const std::array<std::array<int,7>,2> F = {{
    {73,82,3,6,27,54,100},
    {21,62,104,17,50,96,67}
}};
void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(message);
}
bool member(const Mask& m, int x) {
    return (m[x/64] >> (x%64)) & U64(1);
}
void insert(Mask& m, int x) {
    m[x/64] |= U64(1) << (x%64);
}
std::uint32_t encode(std::vector<int> values) {
    std::sort(values.begin(),values.end());
    std::uint32_t result=0;
    for (int x: values) result=result*128+unsigned(x);
    return result;
}

// All feasible sets of exactly three or four auxiliary projected values.
// prefix[k] contains ALL subsets of all feasible sets of size <= k.
struct Catalogues {
    std::array<std::unordered_set<std::uint32_t>,2> prefix;
    std::array<U64,2> counts{};
};
bool xor_closure(const std::array<int,7>& goals,
                 const std::vector<int>& extra) {
    std::array<bool,128> present{};
    std::vector<int> available, todo(goals.begin(),goals.end());
    for (int i=0;i<7;i++) {
        present[1<<i]=true;
        available.push_back(1<<i);
    }
    todo.insert(todo.end(),extra.begin(),extra.end());
    std::size_t added=0;
    while (added<todo.size()) {
        bool progress=false;
        for (int x: todo) {
            if (present[x]) continue;
            bool ready=false;
            for (int a: available) {
                if (present[x^a]) { ready=true; break; }
            }
            if (ready) {
                present[x]=true;
                available.push_back(x);
                added++;
                progress=true;
            }
        }
        if (!progress) return false;
    }
    return true;
}
Catalogues generate_catalogues(int orientation) {
    const auto& goals=F[orientation];
    std::array<bool,128> excluded{};
    excluded[0]=true;
    for (int i=0;i<7;i++) excluded[1<<i]=true;
    for (int x: goals) excluded[x]=true;
    std::vector<int> options;
    for (int x=1;x<128;x++) if (!excluded[x]) options.push_back(x);
    require(options.size()==113,"Wrong auxiliary domain");
    Catalogues out;
    for (int k=3;k<=4;k++) {
        std::vector<int> chosen;
        std::function<void(int)> visit = [&](int first) {
            if (int(chosen.size())==k) {
                if (!xor_closure(goals,chosen)) return;
                out.counts[k-3]++;
                for (unsigned bits=0;bits<(1u<<k);bits++) {
                    std::vector<int> subset;
                    for (int i=0;i<k;i++)
                        if ((bits>>i)&1u) subset.push_back(chosen[i]);
                    out.prefix[k-3].insert(encode(subset));
                }
                return;
            }
            int last=int(options.size())-k+int(chosen.size());
            for (int i=first;i<=last;i++) {
                chosen.push_back(options[i]);
                visit(i+1);
                chosen.pop_back();
            }
        };
        visit(0);
    }
    out.prefix[1].insert(out.prefix[0].begin(),out.prefix[0].end());
    require(out.counts[0]==298,"Triple catalogue mismatch");
    U64 expected=orientation==0 ? 21687 : 21823;
    require(out.counts[1]==expected,"Quadruple catalogue mismatch");
    return out;
}

// State describes only core rows and their previously available FULL values.
struct State {
    std::array<std::uint16_t,5> row{};
    std::array<U64,8> appeared{};
    std::uint8_t changed=0, returned=0, copied=0, extra=0;
    bool operator==(const State& b) const {
        return row==b.row && appeared==b.appeared &&
               changed==b.changed && returned==b.returned &&
               copied==b.copied && extra==b.extra;
    }
};
struct Hash {
    std::size_t operator()(const State& s) const {
        U64 h=1469598103934665603ULL;
        auto add=[&](U64 x) { h^=x; h*=1099511628211ULL; h^=h>>29; };
        for (auto x:s.row) add(x);
        for (auto x:s.appeared) add(x);
        add(s.changed); add(s.returned); add(s.copied); add(s.extra);
        return std::size_t(h);
    }
};
bool has_full(const State& s,int x) {
    return (s.appeared[x/64]>>(x%64)) & U64(1);
}
void remember(State& s,int x) {
    s.appeared[x/64] |= U64(1)<<(x%64);
}
Mask projected(const State& s) {
    Mask m{};
    for (int i=0;i<8;i++) m[i%2] |= s.appeared[i];
    return m;
}
std::vector<int> xor_cost(const State& s,int dimension) {
    std::vector<int> cost(1<<dimension,999);
    cost[0]=0;
    for (int v=1;v<(1<<dimension);v++) if (has_full(s,v)) {
        // Exact zero/one update: pairs {x,x xor v} are disjoint.
        for (int x=0;x<(1<<dimension);x++) if (x<(x^v)) {
            int a=cost[x], b=cost[x^v];
            cost[x]=std::min(a,b+1);
            cost[x^v]=std::min(b,a+1);
        }
    }
    return cost;
}
struct Case {
    int orientation=0, family=0;
    std::vector<int> source, relay;
};
std::vector<Case> make_cases() {
    std::vector<Case> all;
    for (int a=0;a<6;a++) for (int b=a+1;b<6;b++)
        for (int c=0;c<6;c++) for (int d=c+1;d<6;d++)
            all.push_back({0,0,{a,b},{c,d}});
    for (int a=0;a<6;a++) for (int b=a+1;b<6;b++)
        for (int c=0;c<6;c++) all.push_back({1,1,{a,b},{c}});
    for (int a=0;a<6;a++) for (int b=0;b<6;b++)
        all.push_back({0,2,{a},{b}});
    for (int o=0;o<2;o++) for (int a=0;a<6;a++)
        all.push_back({o,3,{a},{}});
    require(all.size()==363,"Case cover size mismatch");
    return all;
}
struct Result {
    std::vector<U64> layers;
    U64 terminals=0, total=0;
    int best=999;
};
Result compute(const Case& c,const Catalogues& catalog) {
    int ns=int(c.source.size()), ny=int(c.relay.size());
    int nc=ns+1+ny, dimension=7+ny, maxdepth=12+ny;
    int slack=2-ns;
    std::vector<int> fixed, want, passive;
    for (int i=0;i<6;i++)
        if (std::find(c.source.begin(),c.source.end(),i)==c.source.end())
            fixed.push_back(1<<i);
    for (int i:c.source) want.push_back(1<<i);
    want.push_back(F[c.orientation][6]);
    for (int j=0;j<ny;j++)
        want.push_back((1<<(7+j)) ^ F[c.orientation][c.relay[j]]);
    for (int j=0;j<6;j++)
        if (std::find(c.relay.begin(),c.relay.end(),j)==c.relay.end())
            passive.push_back(F[c.orientation][j]);
    Mask base{}, output{};
    insert(base,0);
    for (int i=0;i<7;i++) insert(base,1<<i);
    for (int f:F[c.orientation]) insert(output,f);
    State initial;
    for (int i=0;i<ns;i++) initial.row[i]=1<<c.source[i];
    initial.row[ns]=64;
    for (int j=0;j<ny;j++) initial.row[ns+1+j]=1<<(7+j);
    for (int i=0;i<dimension;i++) remember(initial,1<<i);
    std::unordered_set<State,Hash> current, next;
    current.insert(initial);
    Result result;
    State beststate;
    int bestdepth=-1;
    for (int depth=0;depth<=maxdepth;depth++) {
        const State* diagnostic = nullptr;
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
                          << " " << int(diagnostic->extra) << "\n";
            }
        }
        result.layers.push_back(current.size());
        result.total+=current.size();
        for (const State& s:current) {
            if (s.changed!=((1<<ns)-1)) continue;
            bool terminal=true;
            for (int i=0;i<nc;i++) if (s.row[i]!=want[i]) terminal=false;
            if (!terminal) continue;
            result.terminals++;
            auto cost=xor_cost(s,dimension);
            int length=depth;
            for (int f:passive) length+=cost[f];
            if (length < result.best) {
                result.best=length;
                beststate=s;
                bestdepth=depth;
            }
        }
        if (depth==maxdepth || current.empty()) break;
        next.clear();
        next.reserve(current.size()*2+1);
        for (const State& s:current) {
            Mask old=projected(s);
            std::vector<int> aux;
            for (int p=1;p<128;p++)
                if (member(old,p)&&!member(base,p)&&!member(output,p))
                    aux.push_back(p);
            for (int t=0;t<nc;t++)
            for (int j=0;j<nc+int(fixed.size());j++) {
                if (j==t) continue;
                int control=j<nc ? s.row[j] : fixed[j-nc];
                int value=s.row[t]^control, p=value&127;
                if (value==0) continue;
                State nextstate=s;
                bool mandatory=false;
                if (t<ns) {
                    nextstate.changed|=1<<t;
                    if (value==(1<<c.source[t]) &&
                        ((s.changed>>t)&1) && !((s.returned>>t)&1)) {
                        nextstate.returned|=1<<t;
                        mandatory=true;
                    }
                }
                if (t>ns && (s.row[t]&127)==0 && p!=0 &&
                    !((s.copied>>(t-ns-1))&1)) {
                    nextstate.copied|=1<<(t-ns-1);
                    mandatory=true;
                }
                bool seen=member(base,p)||member(old,p);
                if (seen&&!mandatory) nextstate.extra++;
                if (nextstate.extra>slack) continue;
                auto enlarged=aux;
                if (!seen&&!member(output,p)) enlarged.push_back(p);
                int capacity=5-ns-nextstate.extra;
                if (int(enlarged.size())>capacity) continue;
                const auto& allowed=catalog.prefix[capacity<=3 ? 0 : 1];
                if (!allowed.count(encode(enlarged))) continue;
                nextstate.row[t]=value;
                remember(nextstate,value);
                if (slack==0) {
                    Mask known=projected(nextstate);
                    bool valid=true;
                    for (int i=ns;i<nc && valid;i++) {
                        int f=want[i]&127;
                        if (!member(known,f)||nextstate.row[i]==want[i])
                            continue;
                        if (i==ns || (nextstate.row[i]&127)!=0) {
                            valid=false;
                            break;
                        }
                        bool clean=false;
                        for (int j2=0;j2<nc;j2++)
                            if (nextstate.row[j2]==f) clean=true;
                        if (!clean) valid=false;
                    }
                    for (int f:passive)
                        if (member(known,f)&&!has_full(nextstate,f))
                            valid=false;
                    if (!valid) continue;
                }
                int different=0, untouched=0;
                std::set<int> missing;
                for (int i=0;i<nc;i++) if (nextstate.row[i]!=want[i]) {
                    different++;
                    int increment=nextstate.row[i]^want[i];
                    bool available=false;
                    for (int j2=0;j2<nc;j2++)
                        if (nextstate.row[j2]==increment ||
                            want[j2]==increment) available=true;
                    for (int f:fixed) if (f==increment) available=true;
                    if (!available) missing.insert(increment);
                }
                for (int i=0;i<ns;i++)
                    if (!((nextstate.changed>>i)&1)) untouched++;
                int bound=std::max(different+2*untouched,
                           different+(int(missing.size())+1)/2);
                if (depth+1+bound>maxdepth) continue;
                if (diagnostic == &s) {
                    std::cout << "EDGE " << depth << " " << t << " " << j;
                    for (int i=0;i<nc;i++) std::cout << " " << nextstate.row[i];
                    for (U64 x : nextstate.appeared) std::cout << " " << x;
                    std::cout << " " << int(nextstate.changed)
                              << " " << int(nextstate.returned)
                              << " " << int(nextstate.copied)
                              << " " << int(nextstate.extra) << "\n";
                }
                next.insert(nextstate);
            }
        }
        current.swap(next);
    }
    if (bestdepth>=0) {
        std::cout << "TERMINAL " << bestdepth << " " << result.best
                  << " " << ns << " " << ny;
        for (int i=0;i<nc;i++) std::cout << " " << beststate.row[i];
        for (U64 x : beststate.appeared) std::cout << " " << x;
        std::cout << " " << int(beststate.changed)
                  << " " << int(beststate.returned)
                  << " " << int(beststate.copied)
                  << " " << int(beststate.extra) << "\n";
    }
    return result;
}

void foundations() {
    std::vector<int> span{0};
    for (int f:{73,82,100}) {
        auto copy=span;
        for (int x:copy) span.push_back(x^f);
    }
    std::sort(span.begin(),span.end());
    require(std::set<int>(span.begin(),span.end()).size()==8,"Rank of H");
    std::set<int> start, forms, cosets;
    for (int i=0;i<7;i++) start.insert(1<<i);
    forms=start;
    forms.insert(F[0].begin(),F[0].end());
    int outside=0;
    for (int x:forms) {
        if (std::binary_search(span.begin(),span.end(),x)) continue;
        outside++;
        int representative=127;
        for (int h:span) representative=std::min(representative,x^h);
        require(representative!=0,"Zero coset");
        cosets.insert(representative);
    }
    for (int x:start)
        require(!std::binary_search(span.begin(),span.end(),x),"Input in H");
    require(outside==9&&cosets.size()==9,"Coset condition");
    const std::array<std::array<int,2>,10> xor_program = {{
        {1,8},{2,16},{4,32},{9,64},{18,64},
        {36,64},{1,2},{2,4},{9,18},{18,36}
    }};
    auto available=start;
    for (auto op:xor_program) {
        require(available.count(op[0])&&available.count(op[1]),"XOR input");
        require(!available.count(op[0]^op[1]),"XOR repeat");
        available.insert(op[0]^op[1]);
    }
    for (int f:F[0]) require(available.count(f),"XOR output");
    for (int j=0;j<7;j++) {
        int column=0;
        for (int i=0;i<7;i++) column|=((F[0][i]>>j)&1)<<i;
        require(column==F[1][j],"Transposition mismatch");
    }
    for (int u=0;u<=2;u++) for (int v=0;v<=2;v++)
        require(16+v+std::min(4,6-u-v)>=20,"Zero-sided bound");
    const std::array<std::array<int,2>,19> witness = {{
        {0,9},{1,9},{1,10},{2,10},{2,12},{5,12},
        {3,0},{0,11},{4,1},{1,11},{1,12},{1,7},{0,6},
        {8,7},{8,6},{2,8},{5,8},{4,1},{3,0}
    }};
    std::array<int,13> rows{};
    for (int i=0;i<13;i++) rows[i]=1<<i;
    for (auto g:witness) rows[g[1]]^=rows[g[0]];
    require(rows==TARGET,"19-gate witness mismatch");
    // Check that both normalized 13-row tasks are the stated full endpoints.
    std::array<std::array<int,13>,2> order = {{
        {0,1,2,3,4,5,8,6,7,9,10,11,12},
        {6,7,9,10,11,12,8,0,1,2,3,4,5}
    }};
    for (int o=0;o<2;o++) for (int i=0;i<13;i++) {
        int rowmask=0;
        for (int j=0;j<13;j++) {
            int bit=o==0 ? (TARGET[order[o][i]]>>order[o][j])&1
                         : (TARGET[order[o][j]]>>order[o][i])&1;
            rowmask|=bit<<j;
        }
        int expected=i<6 ? 1<<i : (i==6 ? F[o][6]
                                           : (1<<i)^F[o][i-7]);
        require(rowmask==expected,"Normalized full matrix mismatch");
    }
}
std::mutex output_mutex;
void print_case(int id,const Case& c,const Result& r) {
    std::lock_guard<std::mutex> guard(output_mutex);
    std::cout<<"CASE {\"id\":"<<id<<",\"orientation\":"<<c.orientation
             <<",\"family\":"<<c.family<<",\"layers\":[";
    for (std::size_t i=0;i<r.layers.size();i++) {
        if (i) std::cout<<",";
        std::cout<<r.layers[i];
    }
    std::cout<<"],\"total\":"<<r.total<<",\"terminals\":"<<r.terminals
             <<",\"best\":"<<r.best<<",\"status\":\""
             <<(r.best>18?"zero_support":"positive")<<"\"}"<<std::endl;
}
int main(int argc,char** argv) {
    try {
        foundations();
        std::array<Catalogues,2> catalog =
            {generate_catalogues(0),generate_catalogues(1)};
        std::cout<<"CATALOGUES 298 21687 298 21823\nFOUNDATIONS_OK\n";
        auto cases=make_cases();
        if (argc==3&&std::string(argv[1])=="--one") {
            int id=std::stoi(argv[2]);
            require(id>=0&&id<int(cases.size()),"Invalid case index");
            auto r=compute(cases[id],catalog[cases[id].orientation]);
            print_case(id,cases[id],r);
            std::cout<<"PARTIAL_CHECK_ONLY\n";
            return r.best>18?0:1;
        }
        require(argc<=2,"Usage: hgp13_verify [jobs], or --one index");
        int jobs=argc==2?std::stoi(argv[1]):1;
        require(jobs>=1&&jobs<=8,"jobs must be 1 to 8");
        std::vector<Result> results(cases.size());
        std::atomic<int> cursor{0};
        std::atomic<bool> failed{false};
        std::exception_ptr error;
        std::mutex error_mutex;
        std::vector<std::thread> pool;
        for (int j=0;j<jobs;j++) pool.emplace_back([&]() {
            try {
                while (!failed.load()) {
                    int id=cursor.fetch_add(1);
                    if (id>=int(cases.size())) break;
                    results[id]=compute(cases[id],catalog[cases[id].orientation]);
                    print_case(id,cases[id],results[id]);
                }
            } catch (...) {
                std::lock_guard<std::mutex> guard(error_mutex);
                if (!error) error=std::current_exception();
                failed.store(true);
            }
        });
        for (auto& thread:pool) thread.join();
        if (error) std::rethrow_exception(error);
        std::array<U64,4> numbers{}, totals{}, terminals{}, maxima{};
        U64 total=0;
        for (std::size_t id=0;id<cases.size();id++) {
            const auto& r=results[id];
            require(!r.layers.empty(),"An uncomputed case remains");
            require(r.best>18,"A candidate of length <=18 remains");
            int f=cases[id].family;
            numbers[f]++; totals[f]+=r.total; terminals[f]+=r.terminals;
            maxima[f]=std::max(maxima[f],*std::max_element(r.layers.begin(),r.layers.end()));
            total+=r.total;
        }
        for (int f=0;f<4;f++)
            std::cout<<"FAMILY "<<f<<" CASES "<<numbers[f]
                     <<" LABELS "<<totals[f]<<" MAX_LAYER "<<maxima[f]
                     <<" TERMINALS "<<terminals[f]<<"\n";
        std::cout<<"COMPLETED "<<cases.size()<<" TOTAL_LABELS "<<total<<"\n"
                 <<"VERIFIED_FIXED_MATRIX_MINIMUM_19\n";
        return 0;
    } catch (const std::exception& e) {
        std::cerr<<"VERIFICATION_FAILED: "<<e.what()<<"\n";
        return 1;
    }
}
