// Adapter interface around the unmodified HalftimeHash header.
// Every hash evaluation in this harness goes through these functions, which
// call only the header's own public entry points.
#pragma once
#include <cstddef>
#include <cstdint>

// advanced::V1<3> / V2<3> / V3<3> / V4<3>  (24-byte output), b = 1,2,4,8.
void hh_core24(unsigned b, const uint64_t* key, const char* msg, size_t len,
               uint64_t out[3]);
// Same, but with the one-leaf length baked in as a compile-time constant.
void hh_core24_leaf(unsigned b, const uint64_t* key, const char* msg, uint64_t out[3]);

// HalftimeHashStyle64 / 128 / 256 / 512, b = 1,2,4,8.
uint64_t hh_style(unsigned b, const uint64_t* key, const char* msg, size_t len);

size_t hh_wrapper_key_words();          // kEntropyBytesNeeded / 8
const char* hh_dispatch_name(unsigned b);  // which VjXxx the build selected
