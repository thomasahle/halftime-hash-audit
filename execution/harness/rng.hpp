// AES-128 counter-mode keystream, used as the key-array generator.
// The 128-bit AES key is drawn once per run from getrandom(2) (the kernel
// CSPRNG) and printed in the log; each worker thread uses a distinct 64-bit
// stream id, so the streams are disjoint slices of one AES-CTR keystream.
// A FIPS-197 known-answer test runs before any measurement.
#pragma once
#include <wmmintrin.h>
#include <emmintrin.h>
#include <cstdint>
#include <cstring>

class AesCtr {
  __m128i rk_[11];
  uint64_t ctr_ = 0;
  uint64_t stream_;

  template <int RC>
  static __m128i expand(__m128i k) {
    __m128i t = _mm_aeskeygenassist_si128(k, RC);
    t = _mm_shuffle_epi32(t, 0xff);
    k = _mm_xor_si128(k, _mm_slli_si128(k, 4));
    k = _mm_xor_si128(k, _mm_slli_si128(k, 4));
    k = _mm_xor_si128(k, _mm_slli_si128(k, 4));
    return _mm_xor_si128(k, t);
  }

 public:
  AesCtr(const unsigned char seed[16], uint64_t stream) : stream_(stream) {
    rk_[0] = _mm_loadu_si128(reinterpret_cast<const __m128i*>(seed));
    rk_[1] = expand<0x01>(rk_[0]);  rk_[2] = expand<0x02>(rk_[1]);
    rk_[3] = expand<0x04>(rk_[2]);  rk_[4] = expand<0x08>(rk_[3]);
    rk_[5] = expand<0x10>(rk_[4]);  rk_[6] = expand<0x20>(rk_[5]);
    rk_[7] = expand<0x40>(rk_[6]);  rk_[8] = expand<0x80>(rk_[7]);
    rk_[9] = expand<0x1b>(rk_[8]);  rk_[10] = expand<0x36>(rk_[9]);
  }

  void encrypt_block(const unsigned char in[16], unsigned char out[16]) const {
    __m128i x = _mm_xor_si128(_mm_loadu_si128(reinterpret_cast<const __m128i*>(in)), rk_[0]);
    for (int r = 1; r < 10; ++r) x = _mm_aesenc_si128(x, rk_[r]);
    _mm_storeu_si128(reinterpret_cast<__m128i*>(out), _mm_aesenclast_si128(x, rk_[10]));
  }

  // Fill `words` 64-bit words with fresh keystream.
  void fill(uint64_t* dst, size_t words) {
    while (words >= 16) {
      __m128i x[8];
      for (int j = 0; j < 8; ++j) x[j] = _mm_xor_si128(_mm_set_epi64x(stream_, ctr_ + j), rk_[0]);
      ctr_ += 8;
      for (int r = 1; r < 10; ++r)
        for (int j = 0; j < 8; ++j) x[j] = _mm_aesenc_si128(x[j], rk_[r]);
      for (int j = 0; j < 8; ++j)
        _mm_storeu_si128(reinterpret_cast<__m128i*>(dst + 2 * j), _mm_aesenclast_si128(x[j], rk_[10]));
      dst += 16; words -= 16;
    }
    if (words) {
      uint64_t tail[16];
      __m128i x[8];
      for (int j = 0; j < 8; ++j) x[j] = _mm_xor_si128(_mm_set_epi64x(stream_, ctr_ + j), rk_[0]);
      ctr_ += 8;
      for (int r = 1; r < 10; ++r)
        for (int j = 0; j < 8; ++j) x[j] = _mm_aesenc_si128(x[j], rk_[r]);
      for (int j = 0; j < 8; ++j)
        _mm_storeu_si128(reinterpret_cast<__m128i*>(tail + 2 * j), _mm_aesenclast_si128(x[j], rk_[10]));
      std::memcpy(dst, tail, words * 8);
    }
  }

  uint64_t next_word() { uint64_t w; fill(&w, 1); return w; }

  // FIPS-197 C.1 AES-128 known-answer test.
  static bool self_test() {
    unsigned char key[16], pt[16], ct[16];
    static const unsigned char want[16] = {0x69,0xc4,0xe0,0xd8,0x6a,0x7b,0x04,0x30,
                                           0xd8,0xcd,0xb7,0x80,0x70,0xb4,0xc5,0x5a};
    for (int i = 0; i < 16; ++i) { key[i] = (unsigned char)i; pt[i] = (unsigned char)(0x11 * i); }
    AesCtr a(key, 0);
    a.encrypt_block(pt, ct);
    return std::memcmp(ct, want, 16) == 0;
  }
};
