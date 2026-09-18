// What the header's own sizing helper reports for a one-leaf width-3 call,
// versus the number of key words the same call actually reads (measured by the
// guard-page probe in run.cpp).
#include <cstdint>
#include <cstdio>
#include "halftime-hash.hpp"
using namespace halftime_hash;
using namespace halftime_hash::advanced;
template <unsigned N> using S = RepeatWrapper<BlockWrapperScalar, N>;
int main() {
  printf("{\"event\":\"entropy_sizing\",\"kEntropyBytesNeeded_words\":%zu",
         kEntropyBytesNeeded / 8);
  printf(",\"w3_b1_helper_words\":%zu", GetEntropyBytesNeeded<BlockWrapperScalar, 3>(168) / 8);
  printf(",\"w3_b2_helper_words\":%zu", GetEntropyBytesNeeded<S<2>, 3>(336) / 8);
  printf(",\"w3_b4_helper_words\":%zu", GetEntropyBytesNeeded<S<4>, 3>(672) / 8);
  printf(",\"w3_b8_helper_words\":%zu", GetEntropyBytesNeeded<S<8>, 3>(1344) / 8);
  printf(",\"w2_b1_helper_words_at_65536\":%zu", GetEntropyBytesNeeded<BlockWrapperScalar, 2>(65536) / 8);
  printf("}\n");
  return 0;
}
