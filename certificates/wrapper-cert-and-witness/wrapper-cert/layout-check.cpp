// Run with NEON disabled on the Mac. The hash header is never edited.
#include "../../halftime-current.hpp"
#include <cstdlib>
#include <iostream>
#include <set>
#include <string>
#include <vector>

namespace a = halftime_hash::advanced;
static const uint64_t* key_begin;
static size_t key_words;
static std::set<size_t> reads;

template <unsigned b>
struct TraceWrapper {
    using Inner = a::RepeatWrapper<a::BlockWrapperScalar, b>;
    using Block = typename Inner::Block;
    static Block LoadOne(uint64_t e) { return Inner::LoadOne(e); }
    static Block LoadBlock(const void* p) {
        const uintptr_t u = reinterpret_cast<uintptr_t>(p);
        const uintptr_t start = reinterpret_cast<uintptr_t>(key_begin);
        if (u >= start && u < start + 8 * key_words) {
            const size_t offset = (u - start) / 8;
            for (unsigned j = 0; j < b; ++j) reads.insert(offset + j);
        }
        return Inner::LoadBlock(p);
    }
};

template <unsigned b>
static void layout() {
    using W = TraceWrapper<b>;
    using E = a::EhcBadger<W, 6, 3, 7, 2>;
    typename W::Block stack[9][8][2]{};
    const int lengths[9] = {8,8,8,8,8,8,8,8,0};
    char tail[144*b]{};
    uint64_t out[2];
    reads.clear();
    E::DfsGreedyFinalizer(stack, lengths, tail, sizeof(tail)-1, key_begin+659, out);
    const size_t end = 659 + 147*b;
    if (*reads.begin() != 659 || *reads.rbegin() != end-1 || reads.size() != 147*b)
        std::abort();
    std::cout << "b=" << b << " finalizer_first=" << *reads.begin()
              << " finalizer_last=" << *reads.rbegin()
              << " distinct_words=" << reads.size() << " output_tables_start=2048\n";
}

static void stack_boundary() {
    using E = a::EhcBadger<a::BlockWrapperScalar, 6, 3, 7, 2>;
    uint64_t stack[9][8][2]{};
    int lengths[9] = {8,8,8,8,8,8,8,8,0};
    char leaf[144]{};
    // This is the reachable control state after C8 leaves. Actual values of stack
    // entries cannot affect the sentinel bug, so a multi-GB input is unnecessary.
    E::DfsTreeHash(leaf, 1, stack, lengths, key_begin);
    std::cout << "after leaf C8+1: ";
    for (int n : lengths) std::cout << n << ' ';
    std::cout << "(no zero sentinel remains)\n" << std::flush;
    uint64_t out[2];
    E::DfsGreedyFinalizer(stack, lengths, leaf, 0, key_begin+147, out);
    std::cout << "unexpected sanitizer survival " << out[0] << '\n';
}

int main(int argc, char** argv) {
    std::vector<uint64_t> keys(halftime_hash::kEntropyBytesNeeded/8, 1);
    key_begin = keys.data(); key_words = keys.size();
    const std::string mode = argc > 1 ? argv[1] : "layout";
    if (mode == "layout") { layout<1>(); layout<2>(); layout<4>(); layout<8>(); }
    if (mode == "boundary") stack_boundary();
    if (mode == "table") {
        const char x = 0;
        std::cout << halftime_hash::HalftimeHashStyle64(keys.data(), &x, 1) << '\n';
    }
}
