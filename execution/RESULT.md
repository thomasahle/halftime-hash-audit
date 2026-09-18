# Independent execution-based verification of two HalftimeHash claims

Everything below was produced by a harness written for this job (`verify2/`), not by the
prior analysis's code.  The header under test is `halftime-current.hpp`, SHA-256
`7ef5dd48f54537b430f85bc1867b23a93551ab1c56415cfcef362d1651956cc3`, byte-identical to
`https://raw.githubusercontent.com/jbapple/HalftimeHash/master/halftime-hash.hpp` as fetched
on 2026-09-18.  **The header was not edited.**  Heavy runs were on the Xeon
(`hardware.normalcomputing.net`, 2 x Xeon Platinum 8375C, 48 cores / 96 threads,
GCC 11.5.0), `nice -n 10`, at most 48 OpenMP threads; the ARM/UBSan checks are local
compiles on an arm64 Mac (Apple clang 17).


## Verdict summary

| claim | verdict | the number |
|---|---|---|
| **(A)** `advanced::V1<3>/V2<3>/V3<3>/V4<3>` collide on the 168b-byte pair (all zero vs. word `6b` = 1) with probability at least 2^-32 | **CONFIRMED** | pooled over the four scalar entry points, **76 collisions in 316,053,236,830 uniform random key arrays** = `2^-31.95`, exact Poisson 95% CI `[2^-32.30, 2^-31.63]`, i.e. `1.03 x 2^-32` |
| the mechanism ("all three outputs coincide whenever `high32(core_key[6]) = 0`") | **CONFIRMED exactly** | `high32(core_key[6])` forced to 0: **268,435,456 / 268,435,456 collisions** at every b; forced nonzero: **0 / 268,435,456** at every b.  In all unconditioned runs, 0 collisions with `high32(core_key[6]) != 0` and 0 non-collisions with it zero |
| **(B)** execution part: overlap search on `HalftimeHashStyle64` / `Style128` | **NO PAIR FOUND** | 0 collisions for the referee's sharpest pair (all-zero, 65536 vs 131072 bytes) in 2^31 keys on Style64 and 2^30 + 2^30 on Style128 (scalar and `V2Sse2` dispatch), and 0 for every variant; positive control fired on 1,073,741,824 / 1,073,741,824 trials |

## 0. Harness, keys, and what "uniform random key array" means here

* Sources: `verify2/hh_api.{hpp,cpp}` (the only TU that includes the header),
  `verify2/rng.hpp`, `verify2/run.cpp`, `verify2/encode_check.cpp`,
  `verify2/entropy_check.cpp`, `verify2/reach.cpp`, `verify2/build.sh`,
  `verify2/analyze.py`, `verify2/mkresult.py`, `verify2/assemble.py`, and the batch drivers
  `verify2/sweep*.sh`.  Logs: `verify2/logs/` (`structure.jsonl` = dispatch / guard-page /
  sizing output; `cond.jsonl`, `phase1.jsonl`, `sweep*.jsonl` = measurement runs;
  `vec_*.json` = cross-ISA vectors; `encode_check.jsonl`, `core2_check.jsonl`).
* **Key generator.** AES-128 in counter mode.  The 128-bit AES key is drawn per run from
  `getrandom(2)` (the Linux kernel CSPRNG) and is printed in every `start` and `result`
  event as `seed_hex`; each OpenMP thread uses a distinct 64-bit stream id, so threads
  consume disjoint slices of one keystream.  A FIPS-197 C.1 AES-128 known-answer test runs
  before any measurement and must pass or the harness aborts.
* **Two builds of the unmodified header.**
  * `run_scalar` — `-DSCALAR_DISPATCH`, which `#undef`s `__SSE2__`, `__AVX2__`,
    `__AVX512F__` in the TU *before* including the header (after `<immintrin.h>` has
    already been pulled in).  The header then takes its own `#else` branch and specializes
    `V1..V4` to `V1Scalar/V2Scalar/V3Scalar/V4Scalar`.  This is the requested scalar path;
    no header line is changed.
  * `run_native` — no undefs, `-march=native`.  On this machine the header selects
    `V1Scalar / V2Sse2 / V3Avx2 / V4Avx512`, i.e. what `advanced::Vj<3>` actually resolves
    to for a user on an AVX-512 x86-64 box.
  * Both builds: `g++ -std=c++17 -O3 -march=native -fwrapv -fno-strict-aliasing -Wall`.
    `-fwrapv` is used because the header's SIMD lane sums add signed lane values and the
    intended arithmetic is modulo 2^64.  **No dispatch aliases were needed on x86-64.**
    Cross-check: `run_scalar vec` and `run_native vec` produce **bit-identical** outputs on
    every test vector (24-byte core for b = 1,2,4,8 x 4 message variants, and
    Style64/128/256/512 at lengths 0, 1, 144, 65536, 131072) — `logs/vec_scalar.json`
    vs `logs/vec_native.json`, `diff` empty.
* **Key read-set, measured not assumed.**  `run guard` places the key array flush against a
  `PROT_NONE` page and binary-searches the smallest prefix that does not fault.  Result, on
  both builds:

  | call | key words actually read | `216 + 6b` |
  |---|---:|---:|
  | `advanced::V1<3>`, 168-byte message | 222 | 222 |
  | `advanced::V2<3>`, 336-byte message | 228 | 228 |
  | `advanced::V3<3>`, 672-byte message | 240 | 240 |
  | `advanced::V4<3>`, 1344-byte message | 264 | 264 |
  | `HalftimeHashStyle64/128/256/512`, 131072-byte message | 5956–6113 (key-dependent, always < 6144) | — |

  So for the (A) experiments, drawing the first `216 + 6b` words uniformly per trial is
  *exactly* equivalent to drawing the whole key array uniformly: nothing beyond that prefix
  can be read.  For the (B) experiments the harness redraws all
  `kEntropyBytesNeeded/8 = 8866` words every trial.

## 1. Reachability

**Is `advanced::Vj<3>` a documented public entry point?  Callable: yes.  Documented: no.**

* **README** (fetched 2026-09-18 from `raw.githubusercontent.com/jbapple/HalftimeHash/master/README.md`),
  in full: *"HalftimeHash is a fast hash function for long strings. It is supplied as a C++
  header-only library. To use it, simply #include "halftime-hash.hpp". See example.cpp. /
  For more, see halftime-hash.tex: "HalftimeHash: Modern Hashing without 64-bit Multipliers
  or Finite Fields"."*  It names no API at all.
* **Header usage comment** (lines 3–29, inside `#if 0`) shows only
  `halftime_hash::HalftimeHashStyle512` with `kEntropyBytesNeeded`.  `example.cpp` in the
  repository is the same program.  The repository's C shim (`halftime-hash.h`,
  `halftime-hash.cpp`) exports only `for_c_HalftimeHashStyle512/256/128/64`.  None of these
  mentions `advanced`, `Vj`, or a 24-byte output.
* **But the symbols are public and unguarded.**  `halftime_hash::advanced::V1<3>`,
  `V2<3>`, `V3<3>`, `V4<3>` are explicit specializations (header `SPECIALIZE_4` macro,
  lines 1089–1150) of `inline` function templates declared in the *named* namespace
  `halftime_hash::advanced` — outside the anonymous namespace that ends at line 975 — with
  no macro gate.  My harness calls exactly `advanced::V1<3>(entropy, msg, len, out)` …
  `advanced::V4<3>(...)` from a separate translation unit, with the header unmodified, and
  it compiles clean under `-Wall` and runs.  The header's only commentary on this namespace
  is the parameter block at lines 440–455, which explains `dimension / in_width /
  encoded_dimension / out_width / fanout` and says "`BlockWrapper` and `fanout` are the only
  parameters an end-user should think about noodling with".
* **What the paper promises for it.**  `halftime-hash.tex` names the variant explicitly:
  "HalftimeHash variants will be specified by their number of output bytes: HalftimeHash16,
  HalftimeHash24, HalftimeHash32, or HalftimeHash40" (l. 134); "In HalftimeHash24,
  `(b, d, e, f, k, p, w) = (8, 7, 9, 8, 3, 2^2, 3)`" (l. 456) — exactly the instantiation
  `advanced::V4<3>` (`dimension 7, in_width 3, encoded_dimension 9, out_width 3, fanout 8`,
  block width 8); "For HalftimeHash24, and for strings less than an exabyte in length, this
  is more than 83 bits of entropy" (l. 504); and "HalftimeHash produces output that is
  collision resistant among strings of the same length" (l. 128).  The witness pair below is
  equal-length, so the same-length caveat does not protect it.
  `advanced::Vj<3>` is the only implementation of HalftimeHash24 in this header.

**Can the Style wrappers reach `Encode3`?  No.**  All four wrappers call
`TabulateAfter<advanced::Vj<2>, 2>`; `Vj<2>` instantiates
`(dimension, in_width, encoded_dimension, out_width) = (6, 3, 7, 2)`, and
`EhcBadger::Encode` dispatches on the template constant `out_width`, so only
`Encode2` can run.  Verified by execution, not only by reading: a `-O0 -g` build with gdb
breakpoints on the first statements of `Encode3` (header line 259) and `Encode2` (line 302),
hashing 65536 zero bytes —

| call | `Encode3` executions | `Encode2` executions |
|---|---:|---:|
| `HalftimeHashStyle64` | **0** | 455 |
| `HalftimeHashStyle512` | **0** | 56 |
| `advanced::V1<3>` (168 bytes) | **1** | 0 |

(455 = 65536/144 leaves at b = 1; 56 = 65536/1152 at b = 8.)  `Encode3<Block>` *is* still
instantiated and emitted in the width-2 build — it is dead code under `out_width == 2`, not
live code.

## 2. (A) — the 24-byte `advanced::Vj<3>` witness

The pair, for each block width b (b = 1, 2, 4, 8 sixty-four-bit words per `Block`):
both messages are **168b bytes** — exactly one width-3 EHC leaf
(`dimension * in_width * sizeof(Block) = 21 * 8b`) and an empty raw tail — one all zero, the
other all zero except that 64-bit word `6b` holds the integer 1 (byte `48b` = 0x01 on this
little-endian ABI).  Equal lengths, so the paper's same-length convention is respected.

### 2.1 The index, re-derived from the header

`advanced::Vj<3>` instantiates `EhcBadger<Wrapper, 7, 3, 9, 3, 8>`.  `Load` reads input
symbol `i`, component `j` from byte offset `(3i + j) * sizeof(Block)`, so with
`sizeof(Block) = 8b` bytes, message 64-bit word `6b` is block index `6b / b = 6`, lane 0 —
that is encoded symbol `i = 2`, component `j = 0`.  `Hash` uses
`entropy_matrix = reinterpret_cast<const uint64_t(*)[in_width]>(entropy)`, so symbol `i`,
component `j` uses `entropy[3i + j]`; symbol 2, component 0 uses **`entropy[6]`**, i.e.
`core_key[6]` counted from the pointer passed to `advanced::Vj<3>`.  This matches PROOF.md's
index; I recomputed it from the header and then confirmed it by execution (§2.3).

`MixNone(input, e)` computes `lo32(input + e) * hi32(input + e)` with 32-bit-lanewise
addition.  With the all-zero message that product is `A * Z` where `e = A + 2^32 Z`; with
word `6b` set to 1 it becomes `((A+1) mod 2^32) * Z`.  The difference is `Z` (or
`-(2^32-1) Z mod 2^64` when `A = 2^32-1`); both multipliers of `Z` are odd, hence invertible
mod 2^64, so the difference vanishes **iff `Z = high32(core_key[6]) = 0`**, whatever every
other key word is.  `Combine3`'s column for encoded symbol 2 is `[1, 0, 1]`, which is
visible in the test vectors: for b = 1 the zero message gives
`out = (1663015871223192364, 9830480098601916636, 4498149353367803851)` and the word-6b
message gives `(3986799225012309358, 9830480098601916636, 8506262858330424549)` — output
word 1 is unchanged, words 0 and 2 move (`logs/vec_scalar.json`).

### 2.2 Why only one encoded symbol changes: the shipped `Encode3` has distance 1

`encode_check` calls the header's own `Encode3<uint64_t>` (and `Encode2<uint64_t>`) on
blocks carrying one bit each, so the printed masks are the exact linear dependence of every
encoded block on the 21 input blocks (`logs/encode_check.jsonl`):

```
io[7] = ( b0, b1, b2 )                       masks 0x1, 0x2, 0x4
io[8] = ( b0^b1, b1^b2, b2^b3 )              masks 0x3, 0x6, 0xc
```

Both parity symbols depend only on input blocks **0..3**, because `DistributeRaw` captures
`iter` *by value* one block (not one symbol) past the start, the 26-iteration `while` loop
XORs that frozen triple an even number of times into `io[7]`, and the six `io[8]` calls
compose to the identity on it.  Single-block flips then give:

| flipped input block | encoded symbols that change |
|---|---:|
| 0 | 3 |
| 3 | 2 |
| **6 (the witness)** | **1** |
| 7 | 1 |
| 18 | 1 |

So the shipped `Encode3` has minimum symbol distance **1**, not the 3 that a `k = 3` EHC
needs (and not even the `encoded_dimension - dimension = 2` the header's own comment at
lines 247–250 promises).  `Encode2` measures distance exactly **2** for every single-block
flip, as claimed elsewhere.  *(Minor correction to the referee's report `§C1`: PROOF.md
§8.1's "first four raw blocks" is right and the referee's "should be six" is not — `iter`
is a `const Block*`, so `iter += 1` advances one block, and `io[7]`/`io[8]` depend on blocks
0–3.  Nothing downstream changes: block 6 is outside both sets either way.)*

### 2.3 Conditioning test: the collision event *is* the key-fibre event

`run cond <b> <log2 N> <threads> zero|nonzero` forces `high32(core_key[6])` to 0 (by
`key[6] &= 0xffffffff`, which leaves the low half and every other word uniform) or to a
uniform nonzero value (by rejection, so the conditional law is exact), and leaves all other
key words uniform.  2^20 trials per cell, on **both** builds (`logs/cond.jsonl`):

| b | dispatch (scalar / native) | `high32(k6)=0`: `word_6b` hits | `high32(k6)!=0`: `word_6b` hits | `word_0` control, either conditioning |
|---|---|---:|---:|---:|
| 1 | V1Scalar / V1Scalar | 1048576 / 1048576 | 0 / 0 | 0 |
| 2 | V2Scalar / V2Sse2 | 1048576 / 1048576 | 0 / 0 | 0 |
| 4 | V3Scalar / V3Avx2 | 1048576 / 1048576 | 0 / 0 | 0 |
| 8 | V4Scalar / V4Avx512 | 1048576 / 1048576 | 0 / 0 | 0 |

Repeated on the scalar build at **2^28 = 268,435,456** trials per cell, same picture exactly:
`word_6b` hits 268,435,456 / 268,435,456 with `high32(core_key[6]) = 0` at every b, and
0 / 268,435,456 with it nonzero; `word_0` 0 / 268,435,456 under both conditionings.

That is: **every** key with `high32(core_key[6]) = 0` makes all three 64-bit outputs equal,
and **no** key with `high32(core_key[6]) != 0` did, in over 2^30 conditioned trials in total.  This
reproduces the interrupted prior job's `zero`/`nonzero` cells (`partial_events.jsonl`)
exactly, with a different harness, a different RNG instance and two dispatch paths.

Because `Pr[high32(core_key[6]) = 0] = 2^-32` exactly for a uniform key word, the fibre
argument gives `eps >= 2^-32` rigorously; the unconditioned runs below are the independent
end-to-end check of that number, not its derivation.

### 2.4 Unconditioned trials

Every trial redraws the full live key prefix (`216 + 6b` words, proved above to be the whole
read set) from AES-128-CTR, then evaluates `advanced::Vj<3>` on the all-zero message and on
each variant and compares all three 64-bit output words.  Runs with the same dispatch symbol
and pair are pooled; each run has its own `getrandom` seed, so their trials and hits add.
`advanced::V1<3>` resolves to `V1Scalar` in *both* builds, which is why there is no separate
b = 1 row in the second table.

**Scalar-dispatch build (`V1Scalar/V2Scalar/V3Scalar/V4Scalar`)**

| b | dispatch | pair | trials | hits | eps | exact Poisson 95% CI | score `log2(21b/eps)` |
|---:|---|---|---:|---:|---|---|---:|
| 1 | `V1Scalar` | word 6b | 90194313216 (2^36.39) | **15** | 2^-32.49 | [2^-33.32, 2^-31.76] | 36.88 |
| 1 | `V1Scalar` | word 6b plus 1 | 90194313216 (2^36.39) | **22** | 2^-31.93 | [2^-32.61, 2^-31.33] | 36.33 |
| 2 | `V2Scalar` | word 6b | 72220322526 (2^36.07) | **15** | 2^-32.16 | [2^-33.00, 2^-31.44] | 37.56 |
| 2 | `V2Scalar` | word 6b plus 1 | 72220322526 (2^36.07) | **15** | 2^-32.16 | [2^-33.00, 2^-31.44] | 37.56 |
| 4 | `V3Scalar` | word 6b | 77500055680 (2^36.17) | **20** | 2^-31.85 | [2^-32.56, 2^-31.22] | 38.24 |
| 4 | `V3Scalar` | word 6b plus 1 | 77500055680 (2^36.17) | **20** | 2^-31.85 | [2^-32.56, 2^-31.22] | 38.24 |
| 8 | `V4Scalar` | word 6b | 76138545408 (2^36.15) | **26** | 2^-31.45 | [2^-32.06, 2^-30.90] | 38.84 |
| 8 | `V4Scalar` | word 6b plus 1 | 76138545408 (2^36.15) | **26** | 2^-31.45 | [2^-32.06, 2^-30.90] | 38.84 |

**The header's own dispatch on this AVX-512 machine — i.e. what `advanced::Vj<3>` compiles to
for an ordinary x86-64 user**

| b | dispatch | pair | trials | hits | eps | exact Poisson 95% CI | score `log2(21b/eps)` |
|---:|---|---|---:|---:|---|---|---:|
| 2 | `V2Sse2` | word 6b | 17179869184 (2^34.00) | **3** | 2^-32.42 | [2^-34.69, 2^-30.87] | 37.81 |
| 2 | `V2Sse2` | word 6b plus 1 | 17179869184 (2^34.00) | **3** | 2^-32.42 | [2^-34.69, 2^-30.87] | 37.81 |
| 4 | `V3Avx2` | word 6b | 17179869184 (2^34.00) | **5** | 2^-31.68 | [2^-33.30, 2^-30.46] | 38.07 |
| 4 | `V3Avx2` | word 6b plus 1 | 17179869184 (2^34.00) | **5** | 2^-31.68 | [2^-33.30, 2^-30.46] | 38.07 |
| 8 | `V4Avx512` | word 6b | 17179869184 (2^34.00) | **7** | 2^-31.19 | [2^-32.51, 2^-30.15] | 38.58 |
| 8 | `V4Avx512` | word 6b plus 1 | 17179869184 (2^34.00) | **7** | 2^-31.19 | [2^-32.51, 2^-30.15] | 38.58 |


**Pooled.**  The four scalar entry points have the same predicted `eps`, so pooling is
meaningful: **76 hits in 316,053,236,830 trials (2^38.20)**, i.e. `eps = 2^-31.953` with exact
Poisson 95% CI `[2^-32.297, 2^-31.630]` — a ratio of **1.033** to `2^-32`.  On the header's own
x86 dispatch (`V2Sse2 / V3Avx2 / V4Avx512`), 15 hits in 51,539,607,552 trials = `2^-31.68`,
CI `[2^-32.52, 2^-30.96]`.

Across every one of these runs: **`hit_when_high32(core_key[6]) != 0` = 0** and
**`miss_when_high32(core_key[6]) = 0` = 0**.  I also re-checked every logged full key
dump across all runs — **212 mode-`A` hit records** — and every single observed collision has
the predicted zero high half (`key[6]` for `word_6b` at every b, and for `word_6b_plus_1` at
b >= 2; `key[7]` for `word_6b_plus_1` at b = 1).  **No collision was observed that the
mechanism does not explain: 212 / 212.**

**The control pairs.**

* `word_6b_plus_1` (the control the task suggested) is *not* a negative control: at b >= 2 it
  changes lane 1 of the same `Block` 6, so it is hashed with the *same* key word
  `core_key[6]`, and the harness confirms it collides on **exactly the same trials** (hit sets
  identical for b = 2, 4, 8; disjoint at b = 1, where it instead depends on `core_key[7]`).
  So it measures the same 2^-32 defect at a second key word rather than controlling for it.
* `word_0` (message word 0 = 1, i.e. input symbol 0) is the real negative control: that block
  is one of the four the parity symbols depend on, so three encoded symbols change and three
  simultaneous NH coincidences would be needed.  Measured: **0 hits in 4,294,967,296 (2^32)
  trials for every b**; pooled over the four b that is 0 hits in 2^34, exact Poisson 95% upper
  bound `2^-32.12`.  On its own that is only a mild separation from `2^-32` (a 2^32-trial run
  expects just one hit under `2^-32`, and sees none with probability 0.37).  The sharp
  separation comes from the conditioning runs, where the two pairs are compared on the *same*
  keys: with `high32(core_key[6])` forced to 0, the witness pair collides on **268,435,456 of
  268,435,456** trials and `word_0` on **0 of 268,435,456**, at every b.

### 2.5 Score

The metric is `bits = min over L of log2(L / eps(L))`, `L` in eight-byte words.  Both witness
messages are `168b` bytes = `21b` words, so this single equal-length pair caps the whole
minimum at `log2(21b / eps)`.  With the rigorous `eps >= 2^-32` from the key-fibre count:

| b | entry point | L = 21b words | score upper bound at eps = 2^-32 | measured score (point) | paper's claim for this variant |
|---:|---|---:|---:|---:|---|
| 1 | `advanced::V1<3>` | 21 | **36.39** | 36.88 | — |
| 2 | `advanced::V2<3>` | 42 | **37.39** | 37.56 | — |
| 4 | `advanced::V3<3>` | 84 | **38.39** | 38.53 | — |
| 8 | `advanced::V4<3>` = HalftimeHash24 | 168 | **39.39** | 38.84 | "more than 83 bits of entropy" |

(The measured point estimates scatter around the `eps = 2^-32` column — above it where the
observed hit count came out below its mean, below it where it came out above.  The `2^-32`
column is the rigorous one: it follows from the exact key-fibre count, which the conditioning
test verifies directly.  Either way the gap to 83 bits is more than 43 bits.)

## 3. (B) — execution part: overlap search on the 64-bit wrappers

This is only the execution task: I did not re-referee the proof (a separate referee report
already did, `halftime-referee/RESULT.md`).  What I did check from the header, because the
search needs it: `TabulateAfter<Hasher, 2>` binds `table` at key word 0 and then advances the
core pointer by `width*256 = 512` words, while its own three `TabulateBytes<8>` calls use
rows 0–7, 8–15 and 16–23, i.e. words 0–6143.  So the core's key words really do start at 512,
inside the eight length-byte tables; the guard-page probe shows the wrappers read at most
~6100 words, always below 6144, so the sixteen output-byte tables (2048–6143) are the only
fresh material and the core never reaches them.

The pairs tested, all with all-zero content:

* `len65536_vs_len131072` — the referee's sharpest pair.  `65536 = 0x10000` and
  `131072 = 0x20000` differ only in byte 2, so the length-table difference is
  `D = K[513] ^ K[514]`, and words 513, 514 are `entropy_matrix[0][1]`, `entropy_matrix[0][2]`
  — EHC symbol-0 key words that both messages' cores read (455 and 910 complete leaves at
  b = 1).  This is the configuration where the overlap is real.
* `len8_vs_len9_zeros`, `len31_vs_len32_zeros` — the complementary extreme.  Running the
  header's own `advanced::Vj<2>` on these inputs (`logs/core2_check.jsonl`) shows the two
  *cores* are bit-identical for 8 vs 9 zero bytes at every b (and for 31 vs 32 at b = 8),
  because the untagged raw tail pads both to the same block sequence.  So here the proof's
  event `C` holds with probability 1 and a collision happens exactly when `D = 0`, whose
  probability is exactly `2^-64`.  This is the sharpest possible `Pr[C and D=0]`, and it is
  still a factor 2 below the `2 * 2^-64` envelope.  (The two extremes cannot be combined:
  making the cores identical requires the lengths to agree in every byte that changes the
  leaf count, which keeps `D` inside table row 0, below word 512 and so outside the core's
  key window.)
* `len8_zero_vs_len8_word0` — equal length, differing content, so `D = 0` identically and
  only the core can collide.
* `POSITIVE_CONTROL_identical` — two separately allocated copies of the same 8 zero bytes.
  This must report a "hit" on every trial, and does; it is the proof that the harness's
  equality test can fire.

### 3.1 Results — 2^30 uniform random key arrays per cell (2^31 for the Style64 main pair)

All 8866 key words redrawn per trial; scalar-dispatch build; 48 threads; seeds in
`verify2/logs/sweep_phase2.jsonl`.

| wrapper | pair | lengths (bytes) | trials | **hits** | exact Poisson 95% upper bound on eps |
|---|---|---|---:|---:|---|
| Style64 (b=1) | `len65536_vs_len131072` *(referee's sharpest)* | 65536 / 131072 | 2^30 + 2^30 (two runs, independent seeds) = **2^31** | **0** | 2^-29.12 |
| Style128 (b=2) | `len65536_vs_len131072` | 65536 / 131072 | 2^30 | **0** | 2^-28.12 |
| Style64 | `len8_vs_len9_zeros` *(identical cores, `Pr[C]=1`)* | 8 / 9 | 2^30 | **0** | 2^-28.12 |
| Style128 | `len8_vs_len9_zeros` | 8 / 9 | 2^30 | **0** | 2^-28.12 |
| Style64 | `len31_vs_len32_zeros` | 31 / 32 | 2^30 | **0** | 2^-28.12 |
| Style128 | `len31_vs_len32_zeros` | 31 / 32 | 2^30 | **0** | 2^-28.12 |
| Style64 | `len8_zero_vs_len8_word0` *(equal length)* | 8 / 8 | 2^30 | **0** | 2^-28.12 |
| Style128 | `len8_zero_vs_len8_word0` | 8 / 8 | 2^30 | **0** | 2^-28.12 |
| Style128 **on the header's own x86 dispatch** (`V2Sse2`) | `len65536_vs_len131072` | 65536 / 131072 | 2^30 | **0** | 2^-28.12 |
| Style64 | `POSITIVE_CONTROL_identical` | 8 / 8 | 2^30 | 1073741824 (100%) | — |
| Style128 | `POSITIVE_CONTROL_identical` | 8 / 8 | 2^30 | 1073741824 (100%) | — |

**Honest reading of the power.**  Zero hits in 2^30 trials gives an exact Poisson 95% upper
bound of `3.689 / 2^30 = 2^-28.12`.  That is all a 2^30-key experiment can say: it excludes
collision probabilities above about `2^-28`, and it cannot distinguish `2^-63` from, say,
`2^-40`.  What it does establish is that the overlap does **not** produce a gross,
`2^-28`-scale break on the pairs where the overlap is sharpest, and the positive control
proves the search would have seen one.  The `2^-63` claim itself rests on the proof, which a
separate referee checked; this run is a consistency check, not a confirmation of the exponent.

## 4. Verdicts

**(A) CONFIRMED.**  For every b in {1, 2, 4, 8}, the public 24-byte entry point
`advanced::Vj<3>` collides on the two 168b-byte messages "all zero" and "all zero except
64-bit word `6b` = 1" with probability at least 2^-32 over a uniform random key array.  Each
of the four entry points was run over **more than 2^36 uniform random key arrays** on the
scalar path (2^36.39, 2^36.07, 2^36.17, 2^36.15 for b = 1, 2, 4, 8) and over 2^34 on the
header's own x86 dispatch; pooled, **76 collisions in 316,053,236,830 trials**, i.e.
`eps = 2^-31.95` with exact Poisson 95% CI `[2^-32.30, 2^-31.63]` — `1.033 x 2^-32`.

The mechanism is exactly the one claimed, and it is not statistical but deterministic: the
shipped `Encode3` has minimum symbol distance **1** at input block 6 (measured directly on
the header's own encoder), so the whole 24-byte output coincides **iff**
`high32(core_key[6]) = 0`.  Forcing that half to zero gives 268,435,456 collisions out of
268,435,456 trials at every b; forcing it nonzero gives 0.  In every unconditioned run,
`hit_when_high32(core_key[6]) != 0 = 0` and `miss_when_high32(core_key[6]) = 0 = 0`, and all
212 logged key dumps match the prediction (212 / 212).  **No observed collision is unexplained.**

In the metric `bits = min_L log2(L / eps)`, this single equal-length witness at `L = 21b`
words caps the score at **36.39 / 37.39 / 38.39 / 39.39** bits for b = 1, 2, 4, 8 (using the
rigorous `eps >= 2^-32`) — against the paper's "more than 83 bits of entropy" for
HalftimeHash24, which is `advanced::V4<3>` (paper parameters `(b,d,e,f,k,p,w) =
(8,7,9,8,3,2^2,3)`).  The gap is more than 43 bits.

**(B) NO PAIR FOUND.**  On `HalftimeHashStyle64` (2^31 keys, two runs with independent seeds)
and `HalftimeHashStyle128` (2^30 keys on the scalar path and another 2^30 on the header's own
`V2Sse2` dispatch), the referee's sharpest overlap pair — all-zero content, lengths 65536 and
131072, whose length-table difference falls on the EHC key words `K[513]`, `K[514]` that both
cores read — produced **0** collisions.  So did every variant: 8 vs 9 zero bytes (whose two
*cores* are bit-identical at every b, so `Pr[C] = 1` and the collision probability is exactly
`2^-64`), 31 vs 32 zero bytes (identical cores at b = 8, differing at b = 1, 2, 4), and an
equal-length differing-content pair.  The positive control (two copies of the
same message) fired on 1,073,741,824 of 1,073,741,824 trials on both wrappers, so the search
was live.  The honest limit of this evidence: 0 hits in 2^30 bounds `eps` only by `2^-28.12`
at 95% confidence (2^-29.12 at 2^31), so the run is consistent with the claimed 2^-63 but
cannot confirm the exponent; what it rules out is a gross overlap-driven break.

## 5. Compilation and platform qualifications (not verdicts)

These are build/source defects observed while doing the work.  None of them is a collision
result, and none of them changes the verdicts above.

1. **Out-of-bounds table subscript (affects the Style wrappers).**  Header line 1025 indexes
   `table[8*(i+1)][0]` on a reference declared at line 1019 as `const uint64_t (&table)[1+width][256]`,
   i.e. `[3][256]` at `width = 2`.  GCC 11.5 with `-O2 -Wall -Wextra -Warray-bounds=2` reports
   `halftime-hash.hpp:1025:47: warning: array subscript 8 is above array bounds of 'const uint64_t [3][256]'`
   and the same for subscript 16.  Apple clang 17 with `-fsanitize=undefined` reports at run
   time, on a single `HalftimeHashStyle64` call:
   `halftime-hash.hpp:1025:60: runtime error: index 8 out of bounds for type 'const uint64_t[3][256]'`.
   The caller's allocation is large enough that no physical overrun occurs, and every build I
   tested generates the intended flat addresses, but the literal wrappers are not portable
   ISO C++.  `libubsan` is not installed on the Xeon, so the UBSan run is the local arm64 one.
   The width-3 core path (`advanced::Vj<3>`) does not go through `TabulateAfter` and produced
   no UBSan diagnostic.
2. **Stock NEON does not compile.**  On arm64 (Apple clang 17), the unmodified header fails:
   `halftime-hash.hpp:1124:1: error: use of undeclared identifier 'V4Neon'` and likewise
   `V3Neon` (1125) and `V2Neon` (1126).  `HASH_WRAP`/`HASH_WRAP_REPEAT` define only
   `V2Sse2/V3Sse2/V4Sse2` for the shared SSE2/NEON block type, while `SPECIALIZE_4(j, Neon)`
   asks for `VjNeon`.  **Recorded shim:** the arm64 checks used the command-line definitions
   `-DV2Neon=V2Sse2 -DV3Neon=V3Sse2 -DV4Neon=V4Sse2` — no header edit.  With that shim the
   arm64/NEON build reproduces the x86-64 values exactly: for one fixed key array,
   `style64 = 17926063739144598105`, `style512 = 10660834198749432173`,
   `core24[0] = 11413788526348411229` on both x86-64 GCC 11.5 `-O0` and arm64 clang 17
   `-O1 -fsanitize=undefined`.  **No dispatch alias was needed for any result reported above**,
   which was all produced on x86-64.
3. **Signed lane sums.**  All builds use `-fwrapv`; the header's SIMD `Sum` helpers add
   signed lane values whose intended arithmetic is modulo 2^64.
4. **The header's own sizing helper under-allocates for the advanced width-3 API.**
   `GetEntropyBytesNeeded<Wrapper,3>(168b)` returns 95 / 140 / 230 / 410 words for
   b = 1/2/4/8 (`entropy_check`), while the guard-page probe shows the same calls read
   222 / 228 / 240 / 264 words: for b = 1, 2, 4 the helper under-reports, so sizing the key
   array with it would make `advanced::Vj<3>` read past the end of the allocation.  (The
   public constant `kEntropyBytesNeeded` = 8866 words is ample and is what the header's
   example uses; all runs here allocate at least that.)  This is an allocation-sizing bug,
   not a collision bug.
5. **The header's usage example seeds with a default-constructed `mt19937_64`**, i.e. a fixed
   61-bit-state PRNG stream, not independent uniform key words.  Every result here assumes
   independent uniform 64-bit key words; nothing is claimed for a seeded expansion.

## 6. Reproduction

```
verify2/build.sh                       # builds run_scalar (SCALAR_DISPATCH) and run_native
./run_scalar info                      # dispatch names, kEntropyBytesNeeded
./run_scalar guard                     # PROT_NONE probe of the key read-set
./run_scalar vec ; ./run_native vec    # cross-ISA test vectors (must diff clean)
./encode_check                         # Encode3 / Encode2 dependence and distance
./core2_check                          # whether a (B) pair shares a core
./entropy_check                        # the header's own sizing helper
./run_scalar cond <b> <log2N> <threads> zero|nonzero
./run_scalar A    <b> <log2N> <threads> pair2|all [max_seconds]
./run_scalar B    <b> <log2N> <threads> main|short|var [max_seconds]
python3 verify2/analyze.py <logs>      # epsilon, exact Poisson 95% CI, score, per run
python3 verify2/assemble.py            # pooled tables + result.json  (mkresult.py = per-run only)
```

The batch drivers actually used were `verify2/sweep.sh` (phases), then `sweep3.sh`,
`sweep4.sh`, `sweep5.sh`, `sweep6.sh` after two interruptions — see the note below.

Each run prints a `start` event (with `seed_hex`, the getrandom-drawn AES key) and one
`result` event per pair (with `trials` = the number of trials actually completed, `hits`, and
the same `seed_hex`).  `hit` events carry the full key array, capped at 64 dumps per pair.
Reachability used `g++ -O0 -g` plus gdb line breakpoints (`verify2/reach.cpp`); the arm64
checks used `clang++ -fsanitize=undefined` with `-DV2Neon=V2Sse2 -DV3Neon=V3Sse2
-DV4Neon=V4Sse2` on the command line.

**Interruptions, disclosed.**  Two things went wrong on the shared Xeon and are visible in the
logs.  (1) My first mode-`B` build logged the full key array on every hit, which for the
`POSITIVE_CONTROL_identical` pair meant every trial; that run was killed, the 26 GB log
deleted, and the harness fixed (a 64-dump cap, taken outside the OpenMP critical section) —
no measurement from that run is used.  (2) The first `A b=8` 2^36 run and one `cond` run were
killed from outside my session after 1928 s, cause unidentified (no OOM in `dmesg`, and the
neighbouring 2600 s runs survived); `b = 8` was therefore redone as four independent 540 s
chunks with separate `getrandom` seeds, whose trials and hits add.  All `result` events carry
the number of trials **actually completed**, so no capped or truncated run is reported at its
requested size.

Numbers reused from the interrupted prior job are cited as `partial_events.jsonl`; everything
else is from `verify2/logs/`.
## 7. Review of the interrupted job's harness (`independent/`)

I read `independent/api.cpp`, `independent/run.cpp`, `independent/aes_rng.hpp` before
writing my own, and re-derived every index from the header rather than from their code.  On
the three points raised:

* **It calls the right API.**  `core24`/`core24_leaf` dispatch to
  `advanced::V1<3>/V2<3>/V3<3>/V4<3>` with a `uint64_t[3]` output, and the comparison
  `same(a,b) = !((a[0]^b[0])|(a[1]^b[1])|(a[2]^b[2]))` tests all three 64-bit words, i.e. the
  full 24 bytes.  Correct.
* **Mode `zero` conditions on exactly the right thing.**  `keys[6] &= 0xffffffffull` clears
  only the high 32 bits of key word 6, leaving its low half and all other words as fresh
  AES-CTR output; `core_key[6]` is the right word (symbol 2, component 0, from
  `entropy_matrix[i][j] = entropy[3i+j]`), which I re-derived from the header and then
  confirmed by execution.  Mode `nonzero` uses rejection sampling, so its conditional law is
  exact rather than a biased `|=`.  Correct.
* **Key-array size.**  Their `216 + 6b` live prefix is exactly what my independent
  `PROT_NONE` guard-page probe measures (222 / 228 / 240 / 264 words), so refreshing only
  that prefix is equivalent to refreshing a uniform full array.  Correct.
* Their AES-128 known-answer test uses the genuine FIPS-197 C.1 vector, and the seed comes
  from `getrandom`.  Correct.
* Two things their runs did **not** cover, which mine add: mode `A` in their driver carries
  only the `word_6b` pair (the control is added only in the conditioned modes), and their
  `NEON_NAMES` aliases were never activated on x86 (their `build.sh` does not define it), so
  no aliasing was in play in their x86 numbers either.

Their `zero`/`nonzero` cells (1048576/1048576 and 0/1048576 for every b) reproduce exactly
under my harness.  Their unconditioned mode-`A` cells (0 hits in 2^25 per b) are consistent
with `eps = 2^-32` — expected 0.008 hits — and are superseded by the runs in §2.4.
