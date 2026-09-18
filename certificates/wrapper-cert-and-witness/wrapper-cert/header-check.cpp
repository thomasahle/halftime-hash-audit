// Read the original header. NEON_DISPATCH_ALIASES changes only three misspelled
// dispatch names, not the arithmetic, encoder, keys, lengths, or hash functions.
#if defined(NEON_DISPATCH_ALIASES)
#define V2Neon V2Sse2
#define V3Neon V3Sse2
#define V4Neon V4Sse2
#endif
#include "../../halftime-current.hpp"
#include <array>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <vector>

namespace a = halftime_hash::advanced;
using HashCore = void (*)(const uint64_t*, const char*, size_t, uint64_t*);
using HashWrap = uint64_t (*)(const uint64_t*, const char*, size_t);

static uint64_t rng(uint64_t& s) {
    s += 0x9e3779b97f4a7c15ULL;
    uint64_t z = s;
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static void require(bool ok, const char* text) {
    if (!ok) { std::cerr << "FAIL: " << text << '\n'; std::exit(1); }
}

template <unsigned b>
static void check_base(const uint64_t* key, uint32_t high, uint32_t low) {
    using W = a::RepeatWrapper<a::BlockWrapperScalar, b>;
    using B = typename W::Block;
    using E = a::EhcBadger<W, 7, 3, 9, 3>;
    std::array<uint64_t, 21 * b> x{}, y{};
    y[6 * b] = 1;
    B ex[3], ey[3];
    E::EhcBaseLayer(reinterpret_cast<const char*>(x.data()),
                   reinterpret_cast<const uint64_t(*)[3]>(key), ex);
    E::EhcBaseLayer(reinterpret_cast<const char*>(y.data()),
                   reinterpret_cast<const uint64_t(*)[3]>(key), ey);
    const uint64_t delta = low == UINT32_MAX ? -uint64_t(UINT32_MAX) * high : high;
    for (unsigned c = 0; c < 3; ++c)
        for (unsigned j = 0; j < b; ++j)
            require(ey[c].it[j] - ex[c].it[j] ==
                    ((j == 0 && c != 1) ? delta : 0), "exact EHC difference");
}

static void witness() {
    const HashCore dispatch[] = {a::V1<3>, a::V2<3>, a::V3<3>, a::V4<3>};
    const HashCore scalar[] = {a::V1Scalar<7,3,9,3>, a::V2Scalar<7,3,9,3>,
                               a::V3Scalar<7,3,9,3>, a::V4Scalar<7,3,9,3>};
    uint64_t seed = 0x136649aae97b025eULL;
    std::vector<uint64_t> key(4096);
    uint64_t digest = 0;
    for (unsigned style = 0; style < 4; ++style) {
        const unsigned b = 1u << style;
        std::vector<uint64_t> x(21 * b, 0), y = x;
        y[6 * b] = 1;
        uint64_t tested_favourable = 0, tested_all = 0;
        for (unsigned trial = 0; trial < 256; ++trial) {
            for (auto& word : key) word = rng(seed);
            const uint32_t lows[] = {0, 1, UINT32_MAX - 1, UINT32_MAX,
                                     uint32_t(rng(seed))};
            const uint32_t highs[] = {0, 1, 2, 0x80000000, UINT32_MAX,
                                      uint32_t(rng(seed))};
            for (uint32_t low : lows) for (uint32_t high : highs) {
                key[6] = (uint64_t(high) << 32) | low;
                switch (b) {
                case 1: check_base<1>(key.data(), high, low); break;
                case 2: check_base<2>(key.data(), high, low); break;
                case 4: check_base<4>(key.data(), high, low); break;
                case 8: check_base<8>(key.data(), high, low); break;
                }
                uint64_t ox[3], oy[3], sx[3], sy[3];
                const auto xc = reinterpret_cast<const char*>(x.data());
                const auto yc = reinterpret_cast<const char*>(y.data());
                dispatch[style](key.data(), xc, 168 * b, ox);
                dispatch[style](key.data(), yc, 168 * b, oy);
                scalar[style](key.data(), xc, 168 * b, sx);
                scalar[style](key.data(), yc, 168 * b, sy);
                for (unsigned c = 0; c < 3; ++c) {
                    require(ox[c] == sx[c] && oy[c] == sy[c], "ISA/scalar identity");
                    if (!high) require(ox[c] == oy[c], "Encode3 full-output witness");
                    digest ^= ox[c] + oy[c];
                }
                ++tested_all;
                tested_favourable += high == 0;
            }
        }
        std::cout << "Encode3 b=" << b << " bytes=" << 168*b
                  << " changed_word=" << 6*b << " fibre_checks=" << tested_all
                  << " favourable_full_collisions=" << tested_favourable << '\n';
    }
    std::cout << "fibre formula: EHC equal iff high32(key[6])=0; "
                 "2^32 / 2^64 word keys, arbitrary remaining keys\n"
              << "deterministic_digest=" << std::hex << digest << std::dec << '\n';
}

static void wrappers() {
    const HashCore cores[] = {a::V1<2>, a::V2<2>, a::V3<2>, a::V4<2>};
    const HashCore scalar[] = {a::V1Scalar<6,3,7,2>, a::V2Scalar<6,3,7,2>,
                               a::V3Scalar<6,3,7,2>, a::V4Scalar<6,3,7,2>};
    const HashWrap wrappers[] = {halftime_hash::HalftimeHashStyle64,
        halftime_hash::HalftimeHashStyle128, halftime_hash::HalftimeHashStyle256,
        halftime_hash::HalftimeHashStyle512};
    std::vector<uint64_t> key(halftime_hash::kEntropyBytesNeeded / 8);
    uint64_t seed = 0x19909aef04b35b15ULL;
    for (auto& k : key) k = rng(seed);
    std::vector<char> data(100000);
    for (auto& c : data) c = char(rng(seed));
    uint64_t digest = 0;
    for (unsigned s = 0; s < 4; ++s) {
        unsigned tested = 0;
        const size_t leaf = 144 * (1u << s);
        for (size_t len : {size_t(0), size_t(1), size_t(8), size_t(9), leaf-1,
                           leaf, leaf+1, 8*leaf, 9*leaf, 72*leaf, size_t(65536),
                           size_t(65537), size_t(99999)}) {
            uint64_t v[2], scalar_v[2];
            cores[s](key.data()+512, data.data(), len, v);
            scalar[s](key.data()+512, data.data(), len, scalar_v);
            require(v[0] == scalar_v[0] && v[1] == scalar_v[1], "core ISA/scalar");
            uint64_t expected = 0;
            const uint64_t sig[] = {uint64_t(len), v[0], v[1]};
            for (unsigned word = 0; word < 3; ++word)
                for (unsigned byte = 0; byte < 8; ++byte)
                    expected ^= key[(8*word + byte)*256 + ((sig[word] >> (8*byte)) & 255)];
            const uint64_t actual = wrappers[s](key.data(), data.data(), len);
            require(actual == expected, "literal wrapper equals flat address formula");
            digest ^= actual;
            ++tested;
        }
        std::cout << "Style" << (64u << s) << " checked_lengths=" << tested << '\n';
    }
    std::cout << "wrapper_digest=" << std::hex << digest << std::dec << '\n';
}

static void encoders() {
    uint64_t x[27]{}, y[27]{};
    y[6] = 1;
    a::Encode3(x); a::Encode3(y);
    unsigned d3 = 0;
    for (unsigned i = 0; i < 9; ++i) {
        bool differs = false;
        for (unsigned j = 0; j < 3; ++j) differs |= x[3*i+j] != y[3*i+j];
        d3 += differs;
    }
    require(d3 == 1, "Encode3 distance witness");
    unsigned min2 = 7;
    for (uint32_t bits = 1; bits < (1u << 18); ++bits) {
        uint64_t z[21]{};
        for (unsigned i = 0; i < 18; ++i) z[i] = (bits >> i) & 1;
        a::Encode2(z);
        unsigned weight = 0;
        for (unsigned i = 0; i < 7; ++i) weight += (z[3*i] | z[3*i+1] | z[3*i+2]) != 0;
        min2 = std::min(min2, weight);
    }
    require(min2 == 2, "Encode2 exhaustive distance");
    std::cout << "Encode2 nonzero_binary_messages=262143 min_symbol_distance=" << min2
              << " Encode3_witness_distance=" << d3 << '\n';
}

int main(int argc, char** argv) {
    static_assert(sizeof(size_t) == 8, "this certificate is for a 64-bit ABI");
    std::cout << "entropy_bytes=" << halftime_hash::kEntropyBytesNeeded << '\n';
#if defined(NEON_DISPATCH_ALIASES)
    std::cout << "build=NEON with dispatch-name aliases (not unmodified NEON dispatch)\n";
#elif defined(__AVX512F__)
    std::cout << "build=shipped x86 AVX512 dispatch\n";
#elif defined(__SSE2__)
    std::cout << "build=shipped x86 SSE2 dispatch\n";
#else
    std::cout << "build=shipped scalar dispatch\n";
#endif
    const std::string mode = argc > 1 ? argv[1] : "all";
    if (mode == "all" || mode == "encoders") encoders();
    if (mode == "all" || mode == "witness") witness();
    if (mode == "all" || mode == "wrappers") wrappers();
    std::cout << "PASS\n";
}
