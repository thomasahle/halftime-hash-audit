// Independent execution harness for two HalftimeHash claims.
// All hashing is done by the unmodified header via hh_api.cpp.
#include "hh_api.hpp"
#include "rng.hpp"

#include <omp.h>
#include <sys/mman.h>
#include <sys/random.h>
#include <signal.h>
#include <setjmp.h>
#include <unistd.h>

#include <atomic>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <algorithm>

static void os_seed(unsigned char* p, size_t n) {
  while (n) {
    ssize_t z = getrandom(p, n, 0);
    if (z <= 0) { fprintf(stderr, "getrandom failed\n"); exit(3); }
    p += z; n -= (size_t)z;
  }
}
static std::string hex16(const unsigned char* s) {
  char b[33]; for (int i = 0; i < 16; ++i) sprintf(b + 2 * i, "%02x", s[i]); b[32] = 0;
  return std::string(b);
}
static double now_s() {
  return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

// ------------------------------------------------------------------ guard test
// Determine the exact number of leading key words the header reads, by putting
// the key array flush against a PROT_NONE page and shrinking it until it faults.
static sigjmp_buf g_jmp;
static void segv(int) { siglongjmp(g_jmp, 1); }

static size_t read_prefix_words(int kind, unsigned b, size_t msg_len, size_t hi) {
  long ps = sysconf(_SC_PAGESIZE);
  size_t span = ((hi * 8 + ps - 1) / ps + 2) * (size_t)ps;
  char* region = (char*)mmap(nullptr, span + ps, PROT_READ | PROT_WRITE,
                             MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (region == MAP_FAILED) { perror("mmap"); exit(3); }
  mprotect(region + span, ps, PROT_NONE);
  std::vector<char> msg(msg_len ? msg_len : 1, 0);
  unsigned char seed[16]; os_seed(seed, 16);
  AesCtr rng(seed, 12345);

  struct sigaction sa {}, old {};
  sa.sa_handler = segv; sigemptyset(&sa.sa_mask); sa.sa_flags = SA_NODEFER;
  sigaction(SIGSEGV, &sa, &old); sigaction(SIGBUS, &sa, nullptr);

  size_t lo = 1, best = 0;
  // binary search the smallest W that does not fault
  size_t a = lo, c = hi;
  while (a <= c) {
    size_t w = a + (c - a) / 2;
    uint64_t* key = (uint64_t*)(region + span - w * 8);
    rng.fill(key, w);
    volatile int faulted = 0;
    if (sigsetjmp(g_jmp, 1) == 0) {
      uint64_t out[3];
      if (kind == 0) hh_core24(b, key, msg.data(), msg_len, out);
      else out[0] = hh_style(b, key, msg.data(), msg_len);
      asm volatile("" :: "r"(out[0]) : "memory");
    } else faulted = 1;
    if (faulted) { a = w + 1; } else { best = w; c = w ? w - 1 : 0; if (w == 0) break; }
  }
  sigaction(SIGSEGV, &old, nullptr);
  munmap(region, span + ps);
  return best;
}

// ------------------------------------------------------------------ messages
static std::vector<char> zeros(size_t n) { return std::vector<char>(n, 0); }
static std::vector<char> one_at_word(size_t n, size_t w) {
  std::vector<char> m(n, 0); uint64_t v = 1; memcpy(m.data() + 8 * w, &v, 8); return m;
}

struct Res { const char* name; uint64_t hits; };

int main(int argc, char** argv) {
  if (!AesCtr::self_test()) { fprintf(stderr, "AES KAT failed\n"); return 3; }
  if (argc < 2) { fprintf(stderr, "usage: run <info|guard|A|cond|B|speed> ...\n"); return 2; }
  std::string mode = argv[1];

  if (mode == "info") {
    printf("{\"event\":\"info\",\"wrapper_key_words\":%zu,\"dispatch\":{", hh_wrapper_key_words());
    unsigned bs[4] = {1, 2, 4, 8};
    for (int i = 0; i < 4; ++i)
      printf("%s\"b%u\":\"%s\"", i ? "," : "", bs[i], hh_dispatch_name(bs[i]));
    printf("},\"aes_kat\":true}\n");
    return 0;
  }

  if (mode == "vec") {
    // Deterministic test vectors: fixed AES key, so the two builds (scalar and
    // native dispatch) can be diffed against each other.
    unsigned char fixed[16]; for (int i = 0; i < 16; ++i) fixed[i] = (unsigned char)(0xA5 ^ i);
    AesCtr rng(fixed, 7);
    std::vector<uint64_t> key(hh_wrapper_key_words());
    rng.fill(key.data(), key.size());
    unsigned bs[4] = {1, 2, 4, 8};
    for (int i = 0; i < 4; ++i) {
      unsigned bb = bs[i];
      std::vector<char> m(168u * bb, 0);
      for (int variant = 0; variant < 4; ++variant) {
        std::fill(m.begin(), m.end(), 0);
        if (variant) { uint64_t v = 1; size_t w[3] = {6 * bb, 6 * bb + 1, 0}; memcpy(m.data() + 8 * w[variant - 1], &v, 8); }
        uint64_t o[3];
        hh_core24(bb, key.data(), m.data(), m.size(), o);
        printf("{\"event\":\"vec\",\"kind\":\"core24\",\"b\":%u,\"variant\":%d,\"out\":[%llu,%llu,%llu]}\n",
               bb, variant, (unsigned long long)o[0], (unsigned long long)o[1], (unsigned long long)o[2]);
      }
      size_t lens[5] = {0, 1, 144, 65536, 131072};
      for (int j = 0; j < 5; ++j) {
        std::vector<char> z(lens[j] ? lens[j] : 1, 0);
        printf("{\"event\":\"vec\",\"kind\":\"style\",\"b\":%u,\"len\":%zu,\"out\":%llu}\n",
               bb, lens[j], (unsigned long long)hh_style(bb, key.data(), z.data(), lens[j]));
      }
    }
    return 0;
  }

  if (mode == "guard") {
    printf("{\"event\":\"guard\"");
    unsigned bs[4] = {1, 2, 4, 8};
    for (int i = 0; i < 4; ++i) {
      unsigned b = bs[i];
      size_t w = read_prefix_words(0, b, 168u * b, 4096);
      printf(",\"core24_b%u_words_read\":%zu,\"core24_b%u_predicted\":%u", b, w, b, 216u + 6u * b);
    }
    for (int i = 0; i < 4; ++i) {
      unsigned b = bs[i];
      size_t w = read_prefix_words(1, b, 131072, hh_wrapper_key_words());
      printf(",\"style_b%u_len131072_words_read\":%zu", b, w);
    }
    printf(",\"wrapper_key_words\":%zu}\n", hh_wrapper_key_words());
    return 0;
  }

  // ---------------------------------------------------------------- common args
  // A:    run A <b> <log2 trials> <threads> [max_seconds]
  // cond: run cond <b> <log2 trials> <threads> <zero|nonzero>
  // B:    run B <b> <log2 trials> <threads> <main|var> [max_seconds]
  // speed:run speed <b> <kind>
  if (argc < 5) { fprintf(stderr, "bad args\n"); return 2; }
  unsigned b = (unsigned)atoi(argv[2]);
  unsigned e = (unsigned)atoi(argv[3]);
  int threads = atoi(argv[4]);
  if (!(b == 1 || b == 2 || b == 4 || b == 8) || e > 62 || threads < 1 || threads > 48) return 2;
  uint64_t trials = 1ull << e;
  std::string sub = (argc > 5) ? argv[5] : "";
  double max_seconds = (argc > 6) ? atof(argv[6]) : 1e18;

  unsigned char seed[16]; os_seed(seed, 16);
  std::string seed_hex = hex16(seed);

  bool is_core = (mode == "A" || mode == "cond");
  size_t words = is_core ? (size_t)(216 + 6 * b) : hh_wrapper_key_words();

  // ---- message set
  std::vector<std::vector<char>> msgs;   // msgs[0] is the reference message
  std::vector<size_t> pa, pb;            // pairs as indices into msgs
  std::vector<const char*> pname;
  size_t n168 = 168u * b;
  if (is_core) {
    msgs.push_back(zeros(n168));                  // 0: all zero
    msgs.push_back(one_at_word(n168, 6 * b));     // 1: word 6b = 1     (claimed witness)
    msgs.push_back(one_at_word(n168, 6 * b + 1)); // 2: word 6b+1 = 1   (task's control)
    pa = {0, 0}; pb = {1, 2};
    pname = {"word_6b", "word_6b_plus_1"};
    if (sub == "all" || mode == "cond") {
      msgs.push_back(one_at_word(n168, 0));       // 3: word 0 = 1 (code-distance control)
      pa.push_back(0); pb.push_back(3);
      pname.push_back("word_0");
    }
  } else if (mode == "B") {
    if (sub == "main") {
      msgs.push_back(zeros(65536)); msgs.push_back(zeros(131072));
      pa = {0}; pb = {1};
      pname = {"len65536_vs_len131072"};
    } else if (sub == "short") {
      msgs.push_back(zeros(8));                 // 0
      msgs.push_back(zeros(9));                 // 1
      msgs.push_back(zeros(31));                // 2
      msgs.push_back(zeros(32));                // 3
      msgs.push_back(zeros(1));                 // 4  byte 0x00
      msgs.push_back(one_at_word(8, 0));        // 5  (8 bytes, word0=1) -> byte 0x01 at len 8
      msgs.push_back(zeros(8));                 // 6  duplicate of 0: positive control
      pa = {0, 2, 0, 0}; pb = {1, 3, 5, 6};
      pname = {"len8_vs_len9_zeros", "len31_vs_len32_zeros", "len8_zero_vs_len8_word0",
               "POSITIVE_CONTROL_identical"};
    } else {
      msgs.push_back(zeros(65536));            // 0
      msgs.push_back(zeros(196608));           // 1
      msgs.push_back(zeros(131072));           // 2
      msgs.push_back(one_at_word(65536, 0));   // 3
      pa = {0, 2, 0}; pb = {1, 1, 3};
      pname = {"len65536_vs_len196608", "len131072_vs_len196608", "len65536_equal_word0"};
    }
  } else if (mode == "speed") {
    // fall through below
  } else { fprintf(stderr, "bad mode\n"); return 2; }

  if (mode == "speed") {
    std::vector<char> m = zeros(is_core ? n168 : 131072);
    std::vector<uint64_t> key(words);
    unsigned char s2[16]; os_seed(s2, 16); AesCtr rng(s2, 0); rng.fill(key.data(), words);
    uint64_t acc = 0; uint64_t n = 0; double t0 = now_s();
    while (now_s() - t0 < 2.0) {
      for (int i = 0; i < 64; ++i) {
        uint64_t o[3];
        if (sub == "core") { hh_core24_leaf(b, key.data(), m.data(), o); acc ^= o[0]; }
        else { acc ^= hh_style(b, key.data(), m.data(), m.size()); }
        ++n;
      }
      rng.fill(key.data(), words);
    }
    double dt = now_s() - t0;
    printf("{\"event\":\"speed\",\"b\":%u,\"kind\":\"%s\",\"hashes\":%llu,\"seconds\":%.4f,"
           "\"hashes_per_sec\":%.1f,\"bytes\":%zu,\"acc\":%llu}\n",
           b, sub.c_str(), (unsigned long long)n, dt, n / dt, m.size(), (unsigned long long)acc);
    return 0;
  }

  size_t npairs = pa.size();
  printf("{\"event\":\"start\",\"mode\":\"%s\",\"b\":%u,\"dispatch\":\"%s\",\"sub\":\"%s\","
         "\"requested_trials\":%llu,\"threads\":%d,\"key_words\":%zu,"
         "\"rng\":\"AES-128-CTR, getrandom seed, stream=thread\",\"seed_hex\":\"%s\"}\n",
         mode.c_str(), b, hh_dispatch_name(b), sub.c_str(), (unsigned long long)trials,
         threads, words, seed_hex.c_str());
  fflush(stdout);

  std::vector<uint64_t> hits(npairs, 0);
  // Cap on full key dumps per pair.  Without it the mode-B positive control
  // (identical messages, hits every trial) would dump 8866 key words per trial.
  const uint64_t kMaxDumps = 64;
  std::vector<std::atomic<uint64_t>> dumps(npairs);
  for (size_t i = 0; i < npairs; ++i) dumps[i].store(0);
  // The mode-B positive control hits on every trial; never take a lock for it.
  std::vector<char> loggable(npairs, 1);
  for (size_t i = 0; i < npairs; ++i)
    loggable[i] = strcmp(pname[i], "POSITIVE_CONTROL_identical") ? 1 : 0;
  uint64_t done_total = 0, cnt_hi32_zero = 0, miss_when_zero = 0, hit_when_nonzero = 0;
  uint64_t cnt_hi32_zero_2 = 0, agree_2 = 0;
  uint64_t checksum = 0;
  unsigned idx2 = (b == 1) ? 7 : 6;   // key word whose high half drives the second variant
  double t0 = now_s();

  omp_set_num_threads(threads);
#pragma omp parallel reduction(+ : done_total, cnt_hi32_zero, miss_when_zero, \
                               hit_when_nonzero, cnt_hi32_zero_2, agree_2) reduction(^ : checksum)
  {
    int tid = omp_get_thread_num();
    AesCtr rng(seed, (uint64_t)tid);
    std::vector<uint64_t> key(words);
    std::vector<uint64_t> local(npairs, 0);
    uint64_t lo = trials * (uint64_t)tid / (uint64_t)threads;
    uint64_t hi = trials * (uint64_t)(tid + 1) / (uint64_t)threads;
    std::vector<uint64_t> h(msgs.size() * 3);

    for (uint64_t t = lo; t < hi; ++t) {
      rng.fill(key.data(), words);
      if (mode == "cond") {
        if (sub == "zero") key[6] &= 0xffffffffull;
        else { while ((key[6] >> 32) == 0) key[6] = rng.next_word(); }  // rejection
      }
      for (size_t m = 0; m < msgs.size(); ++m) {
        uint64_t* o = &h[3 * m];
        o[0] = o[1] = o[2] = 0;
        if (is_core) hh_core24_leaf(b, key.data(), msgs[m].data(), o);
        else o[0] = hh_style(b, key.data(), msgs[m].data(), msgs[m].size());
      }
      checksum ^= h[0];
      if (is_core) {
        bool z = (key[6] >> 32) == 0;
        cnt_hi32_zero += z;
        bool z2 = (key[idx2] >> 32) == 0;
        cnt_hi32_zero_2 += z2;
        for (size_t p = 0; p < npairs; ++p) {
          const uint64_t* x = &h[3 * pa[p]]; const uint64_t* y = &h[3 * pb[p]];
          bool hit = (x[0] == y[0]) && (x[1] == y[1]) && (x[2] == y[2]);
          local[p] += hit;
          if (p == 0) { miss_when_zero += (z && !hit); hit_when_nonzero += (!z && hit); }
          if (p == 1) { agree_2 += (z2 == hit); }
          if (hit && mode != "cond" && loggable[p] && dumps[p].load(std::memory_order_relaxed) < kMaxDumps) {
#pragma omp critical(out)
            if (dumps[p].fetch_add(1) < kMaxDumps) {
              printf("{\"event\":\"hit\",\"mode\":\"%s\",\"b\":%u,\"pair\":\"%s\",\"thread\":%d,"
                     "\"trial\":%llu,\"key6\":%llu,\"key7\":%llu,\"high32_key6\":%u,\"keys\":[",
                     mode.c_str(), b, pname[p], tid, (unsigned long long)t,
                     (unsigned long long)key[6], (unsigned long long)key[7],
                     (unsigned)(key[6] >> 32));
              for (size_t j = 0; j < words; ++j) printf("%s%llu", j ? "," : "", (unsigned long long)key[j]);
              printf("]}\n"); fflush(stdout);
            }
          }
        }
      } else {
        for (size_t p = 0; p < npairs; ++p) {
          bool hit = h[3 * pa[p]] == h[3 * pb[p]];
          local[p] += hit;
          if (hit && loggable[p] && dumps[p].load(std::memory_order_relaxed) < kMaxDumps) {
#pragma omp critical(out)
            if (dumps[p].fetch_add(1) < kMaxDumps) {
              printf("{\"event\":\"hit\",\"mode\":\"B\",\"b\":%u,\"pair\":\"%s\",\"thread\":%d,"
                     "\"trial\":%llu,\"value\":%llu,\"keys\":[",
                     b, pname[p], tid, (unsigned long long)t, (unsigned long long)h[3 * pa[p]]);
              for (size_t j = 0; j < words; ++j) printf("%s%llu", j ? "," : "", (unsigned long long)key[j]);
              printf("]}\n"); fflush(stdout);
            }
          }
        }
      }
      ++done_total;
      if ((t & 0xffff) == 0 && now_s() - t0 > max_seconds) break;
    }
#pragma omp critical(tot)
    for (size_t p = 0; p < npairs; ++p) hits[p] += local[p];
  }
  double dt = now_s() - t0;
  for (size_t p = 0; p < npairs; ++p) {
    printf("{\"event\":\"result\",\"mode\":\"%s\",\"b\":%u,\"dispatch\":\"%s\",\"sub\":\"%s\","
           "\"pair\":\"%s\",\"len_a\":%zu,\"len_b\":%zu,\"trials\":%llu,\"hits\":%llu,"
           "\"high32_key6_zero\":%llu,\"miss_when_zero\":%llu,\"hit_when_nonzero\":%llu,"
           "\"high32_key%u_zero\":%llu,\"variant2_agrees_with_high32\":%llu,"
           "\"key_dumps_emitted\":%llu,\"checksum\":%llu,\"seconds\":%.3f,\"seed_hex\":\"%s\"}\n",
           mode.c_str(), b, hh_dispatch_name(b), sub.c_str(), pname[p],
           msgs[pa[p]].size(), msgs[pb[p]].size(),
           (unsigned long long)done_total, (unsigned long long)hits[p],
           (unsigned long long)cnt_hi32_zero, (unsigned long long)miss_when_zero,
           (unsigned long long)hit_when_nonzero, idx2, (unsigned long long)cnt_hi32_zero_2,
           (unsigned long long)agree_2, (unsigned long long)dumps[p].load(),
           (unsigned long long)checksum, dt, seed_hex.c_str());
  }
  fflush(stdout);
  return 0;
}
