// The ONLY translation unit that includes the header under test.
// The header itself is byte-for-byte unmodified (sha256
// 7ef5dd48f54537b430f85bc1867b23a93551ab1c56415cfcef362d1651956cc3).
//
// SCALAR_DISPATCH: the header's SPECIALIZE_4 chain is driven by __SSE2__ /
// __AVX2__ / __AVX512F__.  Undefining them *before* the include (and after
// <immintrin.h> has already been pulled in, so the intrinsics headers are
// unaffected) makes the header take its own `#else` branch and specialize all
// four of V1..V4 to VjScalar.  No line of the header is changed.
#if defined(__x86_64__) || defined(__x86_64)
#include <immintrin.h>
#endif

#ifdef SCALAR_DISPATCH
#undef __SSE2__
#undef __AVX2__
#undef __AVX512F__
#undef __ARM_NEON
#undef __ARM_NEON__
#endif

#include "halftime-hash.hpp"
#include "hh_api.hpp"

using namespace halftime_hash;

void hh_core24(unsigned b, const uint64_t* k, const char* m, size_t n, uint64_t o[3]) {
  switch (b) {
    case 1: return advanced::V1<3>(k, m, n, o);
    case 2: return advanced::V2<3>(k, m, n, o);
    case 4: return advanced::V3<3>(k, m, n, o);
    case 8: return advanced::V4<3>(k, m, n, o);
  }
  __builtin_trap();
}

// Compile-time length: exactly one width-3 leaf (dimension*in_width*sizeof(Block)
// = 21 * 8b bytes) and a zero-length raw tail.
void hh_core24_leaf(unsigned b, const uint64_t* k, const char* m, uint64_t o[3]) {
  switch (b) {
    case 1: return advanced::V1<3>(k, m, 168u, o);
    case 2: return advanced::V2<3>(k, m, 336u, o);
    case 4: return advanced::V3<3>(k, m, 672u, o);
    case 8: return advanced::V4<3>(k, m, 1344u, o);
  }
  __builtin_trap();
}

uint64_t hh_style(unsigned b, const uint64_t* k, const char* m, size_t n) {
  switch (b) {
    case 1: return HalftimeHashStyle64(k, m, n);
    case 2: return HalftimeHashStyle128(k, m, n);
    case 4: return HalftimeHashStyle256(k, m, n);
    case 8: return HalftimeHashStyle512(k, m, n);
  }
  __builtin_trap();
}

size_t hh_wrapper_key_words() { return kEntropyBytesNeeded / sizeof(uint64_t); }

// Mirrors the header's own SPECIALIZE_4 selection, evaluated in this TU after
// the (optional) undefs, so it reports the branch the header actually took.
const char* hh_dispatch_name(unsigned b) {
#if __AVX512F__
  switch (b) { case 1: return "V1Scalar"; case 2: return "V2Sse2"; case 4: return "V3Avx2"; case 8: return "V4Avx512"; }
#elif __AVX2__
  switch (b) { case 1: return "V1Scalar"; case 2: return "V2Sse2"; case 4: return "V3Avx2"; case 8: return "V4Avx2"; }
#elif __SSE2__
  switch (b) { case 1: return "V1Scalar"; case 2: return "V2Sse2"; case 4: return "V3Sse2"; case 8: return "V4Sse2"; }
#elif defined(__ARM_NEON) || defined(__ARM_NEON__)
  switch (b) { case 1: return "V1Scalar"; case 2: return "V2Neon"; case 4: return "V3Neon"; case 8: return "V4Neon"; }
#else
  switch (b) { case 1: return "V1Scalar"; case 2: return "V2Scalar"; case 4: return "V3Scalar"; case 8: return "V4Scalar"; }
#endif
  return "?";
}
