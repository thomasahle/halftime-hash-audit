// Direct execution of the header's own Encode3 / Encode2 on symbolic (bit-flag)
// blocks: which encoded symbols change when one input block changes.
// Block = uint64_t, one bit per input block, so the printed masks are the exact
// linear dependence of each encoded block on the 21 (resp. 18) input blocks.
#include <cstdint>
#include <cstdio>
#include <cstring>
#include "halftime-hash.hpp"
using namespace halftime_hash::advanced;

int main() {
  // Encode3: 7 input symbols x 3 blocks = 21 input blocks, 9 x 3 = 27 slots.
  {
    uint64_t io[27];
    memset(io, 0, sizeof io);
    for (int i = 0; i < 21; ++i) io[i] = 1ull << i;   // block i carries bit i
    Encode3<uint64_t>(io);
    printf("{\"event\":\"encode3_dependence\",\"parity_blocks\":{");
    for (int s = 7; s <= 8; ++s)
      for (int c = 0; c < 3; ++c)
        printf("%s\"io[%d][%d]\":\"0x%llx\"", (s == 7 && c == 0) ? "" : ",", s, c,
               (unsigned long long)io[3 * s + c]);
    printf("},\"comment\":\"bit i set means encoded block depends on input block i\"}\n");

    // Which encoded blocks change when exactly one input block is flipped?
    for (int flip : {0, 3, 6, 7, 18}) {
      uint64_t a[27], bb[27];
      memset(a, 0, sizeof a); memset(bb, 0, sizeof bb);
      for (int i = 0; i < 21; ++i) { a[i] = 1ull << i; bb[i] = 1ull << i; }
      bb[flip] ^= 0x8000000000000000ull;             // an extra, distinguishing bit
      Encode3<uint64_t>(a); Encode3<uint64_t>(bb);
      int changed_blocks = 0; int changed_symbols = 0;
      for (int s = 0; s < 9; ++s) {
        int any = 0;
        for (int c = 0; c < 3; ++c) if (a[3 * s + c] != bb[3 * s + c]) { ++changed_blocks; any = 1; }
        changed_symbols += any;
      }
      printf("{\"event\":\"encode3_distance\",\"flipped_input_block\":%d,"
             "\"changed_encoded_blocks\":%d,\"changed_encoded_symbols\":%d}\n",
             flip, changed_blocks, changed_symbols);
    }
  }
  // Encode2: 6 input symbols x 3 = 18 input blocks, 7 x 3 = 21 slots.
  for (int flip : {0, 6, 17}) {
    uint64_t a[21], bb[21];
    memset(a, 0, sizeof a); memset(bb, 0, sizeof bb);
    for (int i = 0; i < 18; ++i) { a[i] = 1ull << i; bb[i] = 1ull << i; }
    bb[flip] ^= 0x8000000000000000ull;
    Encode2<uint64_t>(a); Encode2<uint64_t>(bb);
    int cb = 0, cs = 0;
    for (int s = 0; s < 7; ++s) {
      int any = 0;
      for (int c = 0; c < 3; ++c) if (a[3 * s + c] != bb[3 * s + c]) { ++cb; any = 1; }
      cs += any;
    }
    printf("{\"event\":\"encode2_distance\",\"flipped_input_block\":%d,"
           "\"changed_encoded_blocks\":%d,\"changed_encoded_symbols\":%d}\n", flip, cb, cs);
  }
  return 0;
}
