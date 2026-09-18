// Does the untagged width-2 core distinguish the (B) short pairs?  Calls the
// header's own advanced::Vj<2> (the function the Style wrappers tabulate).
#include <cstdint>
#include <cstdio>
#include <vector>
#include "halftime-hash.hpp"
using namespace halftime_hash;
static void core2(unsigned b, const uint64_t* k, const char* m, size_t n, uint64_t o[2]) {
  switch (b) { case 1: return advanced::V1<2>(k,m,n,o); case 2: return advanced::V2<2>(k,m,n,o);
               case 4: return advanced::V3<2>(k,m,n,o); case 8: return advanced::V4<2>(k,m,n,o); }
}
int main() {
  std::vector<uint64_t> key(kEntropyBytesNeeded / 8);
  for (size_t i = 0; i < key.size(); ++i) key[i] = 0x9E3779B97F4A7C15ull * (i + 1) + i * i;
  std::vector<char> z(131072, 0);
  const size_t pairs[][2] = {{8,9},{31,32},{0,1},{65536,131072},{65536,196608}};
  for (unsigned b : {1u, 2u, 4u, 8u})
    for (auto& p : pairs) {
      if (p[1] > z.size()) continue;
      uint64_t a[2], c[2];
      core2(b, key.data() + 512, z.data(), p[0], a);   // core pointer = entropy + width*256
      core2(b, key.data() + 512, z.data(), p[1], c);
      printf("{\"event\":\"core2\",\"b\":%u,\"len_a\":%zu,\"len_b\":%zu,\"cores_identical\":%s}\n",
             b, p[0], p[1], (a[0]==c[0] && a[1]==c[1]) ? "true" : "false");
    }
  return 0;
}
