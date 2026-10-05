#define main hgp13_verifier_main
#include "../hgp13_verify.cpp"
#undef main

int main() {
    const auto cases = make_cases();
    for (const auto& c : cases) {
        std::cout << c.orientation << ' ' << c.family << ' ';
        for (const auto x : c.source) std::cout << x << ',';
        std::cout << ' ';
        for (const auto x : c.relay) std::cout << x << ',';
        std::cout << '\n';
    }
}
