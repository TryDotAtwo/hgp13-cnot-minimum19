#define main hgp13_verifier_main
#include "../hgp13_verify.cpp"
#undef main

int main() {
    for (int orientation = 0; orientation < 2; ++orientation) {
        const auto cat = generate_catalogues(orientation);
        for (int i = 0; i < 2; ++i) {
            std::vector<std::uint32_t> keys(cat.prefix[i].begin(), cat.prefix[i].end());
            std::sort(keys.begin(), keys.end());
            for (const auto key : keys)
                std::cout << orientation << ' ' << (i + 3) << ' ' << key << '\n';
        }
    }
}
