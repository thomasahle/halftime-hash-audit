# Verdict on the supplied HalftimeHash header

**The key overlap is repairable in the proof: all four shipped 64-bit wrapper algorithms certify 63 bits on explicit finite length domains. The reachable 24-byte Encode3 core has a verified collision-probability counterexample.** The literal header also has C++ array-bound and NEON build defects, so the wrapper result needs the execution-contract qualification below.

| Entry point | Collision verdict under the exact flat-address/modular-arithmetic contract | Certified byte domain |
|---|---|---|
| `HalftimeHashStyle64` | **Certified: 63 bits** | `0 <= length < 2,761,050,384` |
| `HalftimeHashStyle128` (the user's `halftime_hash128` benchmark mapping) | **Certified: 63 bits**, returns 64 bits | `0 <= length < 5,522,100,768` |
| `HalftimeHashStyle256` | **Certified: 63 bits** | `0 <= length < 11,044,201,536` |
| `HalftimeHashStyle512` | **Certified: 63 bits** | `0 <= length < 22,088,403,072` |
| `advanced::V1<3>`, `V2<3>`, `V3<3>`, `V4<3>` (24-byte output) | **Advertised bound refuted**, even at equal lengths: fixed pair has collision probability **at least `2^-32`** | Witness lengths 168, 336, 672, 1344 bytes respectively |
| Literal wrappers as a portable ISO C++ program | **Not certified / undefined table indexing** | No nonempty universal portability claim, even below the above limits |
| Unmodified native NEON dispatch | **Build failure**, not a collision verdict | No executable native NEON path in this exact header without dispatch aliases |

Here “63 bits” is a certificate for the full independent uniform key array and the word-cap metric in the question, **not** a constant `2^-63` collision bound at all lengths, a 128-bit output claim, or a proof for a seeded key expansion. It includes unequal lengths. It uses the shipped overlapping offsets without adding independent key material. The original header remains unchanged.

For `b=1,2,4,8` respectively and integer word cap `L`, a rigorous simple wrapper envelope is

```
eps_b(L) = 2^-63                                      for L < 18b,
           ((h+2)(h+5)+1) 2^-64                       otherwise,
h = floor(log_8(floor(L/(18b)))).
```

Its score `min_L log2(L/eps_b(L))` is **63**, attained at `L=1`. Retaining a tiny correction gives the sharp score `64-log2(2-2^-64)`, approximately 63; the one-byte pair `00` / `01` has exact collision probability `2^-63-2^-128`. All sixteen output-byte tables remain fresh: on the safe stack domain the largest core key index is 1834, while output tables start at 2048. Dependence on the overlapping length tables is handled explicitly in [PROOF.md §6](PROOF.md), not assumed away.

**Encode2:** its distance is exactly **2**. The 21 two-column minor certificates give maximum singleton-kernel sum 5 and full kernel size 4. The corrected equal-length 16-byte core bound is `2^-64` below one leaf and `(h+2)(h+5)2^-64` thereafter, scoring **64** before tabulation. See [minor certificates](review-support/wrapper-cert/encode2-minors.json) and [the generator and exact calculations](review-support/wrapper-cert/certificates.py).

**HalftimeHash24:** there is no top-level function with that spelling, but the public `advanced::Vj<3>` specializations reach `Encode3` and return 24 bytes. For block width `b`, compare `168b` zero bytes with the same message whose 64-bit word `6b` is 1 (byte `48b` is `01`, little endian). For every assignment of the other keys, all three outputs collide when `high32(core_key[6])=0`. Exact fibre counting gives `2^32` favourable values of that key word out of `2^64`, hence a full-output collision probability **at least** `2^-32`; it is not claimed to be exactly that value. At one leaf the valuation-corrected reading of the paper's formula is `65*2^-96`; the witness also violates the literal-exponent reading and the >83-bit headline. This is a verified violation, not merely a failed proof step. It does not affect the Style wrappers, which select Encode2.

Verification used the unchanged header on scalar, SSE2 and AVX-512, plus its native NEON operations after three explicitly recorded dispatch-name aliases and `-fwrapv`. Exact counting, rather than a random-key experiment, establishes the witness probability. The selected real-header executions check the algebra and full-hash propagation; their counts are not probability estimates. [Logs and reproduction instructions](review-support/wrapper-cert/README.md) record all qualifications, including the failed unmodified NEON build, table-bound diagnostic, and finite-stack boundary diagnostic.

**What remains unclaimed:** portability of the literal erroneous C++ table view, successful unmodified NEON compilation, safety past the finite stack limit, every original pointwise constant in the paper, and any key-distribution guarantee for a PRNG-seeded subfamily. No overlap-based pair violating the proved wrapper envelope is established; the overlap proof rules one out under its stated contract. The Encode3 witness is a separate, actual break of the advertised 24-byte-core bound.
