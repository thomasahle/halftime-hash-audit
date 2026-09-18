// Execution-based reachability probe, -O0 so the encoder templates are real
// symbols.  argv[1] selects which public API to exercise exactly once.
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>
#include "halftime-hash.hpp"
using namespace halftime_hash;
int main(int argc, char** argv) {
  std::vector<uint64_t> key(kEntropyBytesNeeded / 8, 0);
  for (size_t i = 0; i < key.size(); ++i) key[i] = 0x9E3779B97F4A7C15ull * (i + 1);
  std::vector<char> msg(65536, 0);
  const char* w = argc > 1 ? argv[1] : "style64";
  if (!strcmp(w, "style64"))
    printf("style64=%llu\n", (unsigned long long)HalftimeHashStyle64(key.data(), msg.data(), msg.size()));
  else if (!strcmp(w, "style512"))
    printf("style512=%llu\n", (unsigned long long)HalftimeHashStyle512(key.data(), msg.data(), msg.size()));
  else { uint64_t o[3]; advanced::V1<3>(key.data(), msg.data(), 168, o);
    printf("core24=%llu\n", (unsigned long long)o[0]); }
  return 0;
}
