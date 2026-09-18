# Reproduction and evidence

Read [VERDICT.md](../../VERDICT.md) and [PROOF.md](../../PROOF.md) first. All includes point directly to the unchanged `../../halftime-current.hpp`. The source hash in [results.json](results.json) identifies the exact audited file. These are mathematical certificates plus focused real-header checks, not a random-key collision search.

From the workspace root, the complete Xeon reproduction is:

```bash
bash review-support/wrapper-cert/run-xeon.sh
```

It runs sequentially with `nice -n 10`, one worker at a time, well below the requested 48-thread cap. The recorded remote directory is `thomas-ahle@hardware.normalcomputing.net:~/agents/halftime-wrapper`. It requires Python 3 and Clang; no Python dependencies or network downloads are needed. On this Xeon, `-march=native` enables the header's AVX-512 path. An SSE2 build is checked separately. Both use `-fwrapv` for the header's signed horizontal-sum helpers.

The Mac reproduction is:

```bash
bash review-support/wrapper-cert/run-mac.sh
```

It runs one process at a time. The scalar build explicitly disables both NEON macros. The NEON verification build defines `NEON_DISPATCH_ALIASES`, which supplies exactly these mappings before including the header:

```cpp
#define V2Neon V2Sse2
#define V3Neon V3Sse2
#define V4Neon V4Sse2
```

Those three `Sse2`-named functions use NEON intrinsics on arm64; the header uses a shared type/function naming scheme. No encoder, arithmetic, key offset, length handling, or hash circuit is substituted. This shim is necessary because the **unmodified header does not compile on NEON**. The passing build also uses `-fwrapv`; a separate failing build without that flag records signed-overflow UB in `Sum(u128)`.

## Certificates

* [certificates.py](certificates.py) extends the prior review's subset/minor method. It emits [all 21 Encode2 minor certificates](encode2-minors.json), checks the complete 18-bit input subalphabet, derives the bijective-base-eight boundary, checks key intervals and score minima with exact arithmetic, and counts the two 32-bit-half key fibres for the width-3 witness. Its output is [certificates.log](certificates.log) and [results.json](results.json). The algebra in the proof supplies the unrestricted-width distance theorem and links the counted fibres to full-header collisions.
* [header-check.cpp](header-check.cpp) executes the real Encode2 and Encode3, the width-3 advanced hash APIs, and all public wrappers. The width-3 inputs are fixed one-leaf messages. It checks the exact EHC difference formula and whole-output equality on every tested favourable fibre. It also compares each selected ISA with the scalar implementation of the same style and compares wrapper outputs to the literal flat-table address formula.
* [layout-check.cpp](layout-check.cpp) uses the header's finalizer with a tracing block loader to check the largest key indices. Its boundary mode starts with the reachable stack-length state after `C8` leaves, performs one real tree insertion, and calls the finalizer. The contents of the accumulated nodes cannot affect the control-flow error, so it avoids constructing a multi-gigabyte message. Its table mode calls the actual public wrapper.

## Passing logs

| Log | Result |
|---|---|
| [scalar.log](scalar.log) | Shipped scalar dispatch, all four styles |
| [xeon-sse2.log](xeon-sse2.log) | Shipped SSE2 dispatch and scalar path |
| [xeon-avx512.log](xeon-avx512.log) | Shipped AVX-512 dispatch, with the other style-specific ISA choices |
| [neon-alias.log](neon-alias.log) | Native NEON arithmetic with the three disclosed aliases and `-fwrapv` |
| [layout.log](layout.log) | Last core keys 805, 952, 1246, 1834; output tables start at 2048 |
| [certificates.log](certificates.log) | Exact distance, minors, lengths, score comparisons, and fibre counts |

All four hash-check builds record `deterministic_digest=4cfca77716c818c2` and `wrapper_digest=7a839fa25ab96053`. Per build, per width, the witness check exercises 7,680 key/context cases, including 1,280 favourable full collisions. The surrounding keys come from a fixed deterministic test generator; **these are not uniformly sampled-key probability measurements**. No claim of `2^28` random trials is made or needed: the collision lower bound uses the question's alternative, exact fibre counting, on the full 32-bit halves. The counted event contains `2^32 * (2^64)^(N-1)` of the `(2^64)^N` full keys. We count a subset of the full collision fibre, not all possible additional finalizer collisions.

## Expected failures, also reproduced

| Log | Diagnostic |
|---|---|
| [neon-unmodified-build.log](neon-unmodified-build.log) | Missing `V2Neon`, `V3Neon`, `V4Neon` in stock native build |
| [table-ubsan.log](table-ubsan.log) | Header line 1025: row 8 out of bounds for `uint64_t[3][256]` |
| [boundary-asan.log](boundary-asan.log) | Header line 686: reads past the nine-element `stack_lengths` array after leaf `C8+1` |
| [neon-signed-overflow.log](neon-signed-overflow.log) | Header line 151: signed horizontal lane-sum overflow without `-fwrapv` |

The scripts treat those failures as expected evidence; they are not passing safety checks. The Mac's combined ASan runtime initially hung during its own initialization, before `main`; that run was terminated, its [sample](layout-hang.sample.txt) retained, and all array/stack ASan/UBSan diagnostics were obtained successfully on the Xeon instead. The numerical layout trace is also from the Xeon. This runtime problem supplies no evidence about the header.

Compiler/platform and source hashes are recorded in [mac-environment.log](mac-environment.log) and [xeon-environment.log](xeon-environment.log). Empty `*-build.log` files mean the corresponding successful compiler command emitted no diagnostics. Source and log hashes are listed in [MANIFEST.sha256](MANIFEST.sha256).
