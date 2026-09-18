# HalftimeHash wrapper and Encode3 certificates

This document audits the supplied files, not a replacement implementation. The header SHA-256 is `7ef5dd48f54537b430f85bc1867b23a93551ab1c56415cfcef362d1651956cc3`; it is unchanged and identical to `review-support/sources/halftime-hash.hpp`. The TeX SHA-256 is `3debc6124599a29b6df9839fe43214f67b2dbb057cd3f0a8033f6db5b1903c39`. The starting point is [AUDIT_REVIEW.md §3](AUDIT_REVIEW.md). Primary context is [the paper](https://arxiv.org/abs/2104.08865v2) and [the author's repository](https://github.com/jbapple/HalftimeHash); all implementation conclusions below concern the saved header.

## 1. Scope of the certificate

Set `Q=2^32`, `R=2^64`, `a=1/Q`, and `u=1/R=a²`. All key words are independent uniform 64-bit words. Messages are fixed independently of the key. No result is asserted for a short-seed PRNG expansion. The ABI has eight-byte `size_t`, eight-bit bytes, and little-endian word loading, as on the tested machines.

There are two different implementation questions:

* **The flat-address, modular-arithmetic function performed by the shipped loads:** this has a complete 63-bit wrapper certificate, with the actual overlapping key layout. No independently keyed replacement is used.
* **An unconditional, portable ISO C++ claim about the literal header:** this cannot be made. `TabulateAfter` declares a three-row table and indexes rows 8 and 16. Stock NEON dispatch also fails to compile. SIMD `Sum` uses signed scalar addition on some paths. Section 9 records these issues and the build qualifications. They are not collision attacks.

In particular, a “63-bit certified” result below means the first contract. It must not be quoted as a proof that arbitrary conforming C++ compilers give that function. Tests of selected binaries support the source-to-arithmetic correspondence; they are not a formal verification of every machine instruction or compiler transformation.

For the score, `L` is a positive integer cap in **eight-byte words**; both messages have at most `8L` bytes. The output floor is `2^-64` for the wrappers. The displayed simple envelope has score exactly 63. A slightly sharper envelope and an attaining short pair are given in §7.

## 2. Exact layout, length handling, and the finite stack

Let `b=1,2,4,8` for Style64, Style128, Style256, Style512 respectively. The style number is the block width, not the output width. Every public wrapper returns **64 bits**, calls `V1<2>`, `V2<2>`, `V3<2>`, or `V4<2>`, and instantiates

```
(dimension, in_width, encoded_dimension, out_width, fanout) = (6,3,7,2,8).
```

A block contains `b` 64-bit lanes. An EHC leaf consumes `18b` words, or `144b` bytes. The 21 EHC key words and the tree key words are broadcast across lanes; the finalizer uses distinct words for distinct lanes. These are different key arrangements.

### 2.1 Absolute key indices for the public wrappers

Number the caller's entropy words `K[0],K[1],...`. Ignoring only the erroneous declared array extent, the actual tabulation address formula is

```
H_K(m) = XOR_(j=0..7) K[256j + byte_j(length)]
       XOR_(j=0..7) K[2048 + 256j + byte_j(core[0])]
       XOR_(j=0..7) K[4096 + 256j + byte_j(core[1])].
```

`TabulateAfter` advances the core pointer by `width*256=512` **words**, not 6144 words. Thus:

| Use | Absolute word indices / formula |
|---|---|
| Length-byte tables | `0..2047` |
| EHC NH symbol `(s,t)` | `512+3s+t`, `0<=s<7`, `0<=t<3` |
| Tree level `j`, coordinate `c`, child `v` | `533+14j+7c+(v-1)`, `c=0,1`, `v=1..7` |
| Finalizer start | `512+21+2*7*9 = 659` |
| Core output 0 byte tables | `2048..4095` |
| Core output 1 byte tables | `4096..6143` |

The initial child of a tree node is passed through as the accumulator; only children 1 through 7 use NH keys. The code reserves nine tree levels before the finalizer whether or not those levels are used. It does **not** set the finalizer start using the actual tree height.

If the forest has `s` live nodes, in the exact low-level-first traversal order of `DfsGreedyFinalizer`, stack node `v`, coordinate `c`, lane `ell` uses

`K[659 + b(2v+c) + ell]`.

These consume `2bs` words. The raw suffix starts with key pointer `p=659+2bs`. Raw block `t`, coordinate `c`, lane `ell` uses

`K[p + b(t+c) + ell]`.

This is a Toeplitz shift by **b entire 64-bit NH pairs**, not a shift of a single 32-bit half. If the remaining byte count is `r<144b`, the finalizer inserts `floor(r/(8b))+1` raw blocks. The last block is zero padded; a completely zero block is inserted even when `r` is block aligned or zero. Therefore there are at most 18 raw blocks, and their two outputs use at most `19b` distinct key words. The raw suffix keys start after all forest keys; there is no forest/suffix overlap. The final horizontal lane sum is addition modulo `R` under the stated execution contract.

Neither the EHC/tree core nor this padding includes a length tag. For example, empty input and one zero byte produce the same raw core outputs for every key. Length is accounted for only by the wrapper's first eight tabulation rows. The paper's equal-length convention must therefore be preserved when discussing the unwrapped core.

### 2.2 The exact sentinel-safe length cap

For `n>0` complete leaves, the nonzero stack lengths are the **bijective base-eight digits** of `n`: digits are in `1..8`, lowest first. Indeed, before inserting a new leaf, every initial digit equal to 8 is promoted and cleared; the new low digit is then set to 1, and every newly cleared intermediate digit becomes 1. Induction gives both the representation and the absence of zero holes. The zero-leaf case has all digits zero.

The arrays have nine entries, but the finalizer tests `stack_lengths[j] > 0` without testing `j<9`. It needs a zero sentinel within those nine entries. Consequently a safe contiguous domain is

```
C8 = 8 + 8² + ... + 8⁸ = 19,173,960 complete leaves,
n <= C8,
0 <= byte_length < 144b(C8+1).
```

At `n=C8`, the stack lengths are `[8,8,8,8,8,8,8,8,0]`, with 64 live nodes. At `n=C8+1`, they are nine ones, and the finalizer reads `stack_lengths[9]`. This is a real boundary defect, before all nine levels would themselves overflow. It is incorrect to claim the whole 64-bit byte-length domain, or to give all nine entries to live levels without reserving the sentinel. The control-state reproducer uses the real `DfsTreeHash` and finalizer; it does not allocate or hash a multi-gigabyte input.

For this safe domain, all core reads lie below the exclusive upper bound

`659 + b(2*64 + 19) = 659+147b <= 1835 < 2048`.

The maximum includes the finalizer's always-present padded block. It is attained as a maximum read index when the eight live levels each have length 8 and the raw tail has 18 blocks. Actual tree reads on this domain use levels `j=0..6`, within the reserved range. Some words in the bounding interval are unused. We only need its upper endpoint.

| Wrapper | Exclusive byte limit | Largest integer cap `L` with `8L` below that limit | Last possible core key word |
|---|---:|---:|---:|
| Style64 | 2,761,050,384 | 345,131,297 | 805 |
| Style128 | 5,522,100,768 | 690,262,595 | 952 |
| Style256 | 11,044,201,536 | 1,380,525,191 | 1246 |
| Style512 | 22,088,403,072 | 2,761,050,383 | 1834 |

The public constant supplies 70,928 bytes = 8,866 words on the tested 64-bit ABI, enough for all 6,144 table words and these core accesses. The helper `GetEntropyBytesNeeded(n)` is not an exact access map: in particular its variable-height formula must not replace the fixed nine-level offset when allocating small advanced-core calls. Our advanced-core tests supply 4,096 words. The wrapper theorem uses the public full allocation.

**The essential fact is now exact:** the overlap is entirely with the length tables. All sixteen output-byte tables remain independent of every core computation and of all eight length tables, for both messages.

## 3. NH facts used in the proof

For a 64-bit input word with halves `(x,y)` and a key word with halves `(s,t)`, the code's elementary product is

`N_(s,t)(x,y) = ((x+s) mod Q) ((y+t) mod Q) mod R`.

For different fixed input strings at the same number of pairs, a sum of these products is `a`-almost-difference-universal modulo `R`. Here is the one-pair argument, including carries. In a differing pair select a differing half and condition on its key, so the corresponding two factors `c,c'` are distinct in `[0,Q)`. Condition on all other pairs. Translate the other key to a uniform `k` in `[0,Q)`. Any target equation has the form

`c k - c' ((k+d) mod Q) = v (mod Q²)`.

Within either interval separated by the possible wrap, the nonzero slope `c-c'` gives at most one solution: a nonzero difference has absolute value below `Q²`. If two solutions straddled the wrap, with `0<k2-k1<Q`, their subtraction would give

`(c-c')(k2-k1) + Qc' = 0 (mod Q²)`.

The left side is strictly between 0 and `Q²`, whether `c>c'` or `c<c'`, which is impossible. Thus at most one of the `Q` remaining keys works. This proves the ADU property, including nonzero targets. It applies to the three-word symbol hashes. The modified tree NH is AU: if only its unhashed initial child differs, equality is impossible; otherwise a differing hashed child supplies this ADU bound after the initial-child difference is included in the target.

For the final raw suffix, flatten the lanes into consecutive 64-bit NH pairs. Two outputs use shifts 0 and `b` pairs. Discard the identical suffix in a comparison and choose its last differing pair. The later output has a key pair beyond every key that matters to the earlier output's difference. Conditional on all preceding keys, the same one-pair argument costs `a` for that output. Iteration gives `a²` for a prescribed pair of output differences (or `a³` for three outputs). The always-inserted block and lane sum do not alter this argument. Equal byte lengths ensure that differing byte strings give differing padded pair strings and use identical key offsets.

## 4. Encode2 distance and exact minors

`Encode2` keeps six input symbols `x0,...,x5`, each a triple of blocks, and appends

`x6 = x0 XOR x1 XOR ... XOR x5`.

One changed input symbol changes both itself and the parity symbol. Two or more changed input symbols already give distance at least 2. A single changed input symbol attains distance 2. Thus the **minimum symbol distance is exactly 2**, for any block width. This also holds on an individual differing physical lane. The exhaustive one-bit-per-component check covers all 262,143 nonzero inputs in that subalphabet; the preceding argument proves the unrestricted statement.

The actual `Combine2` matrix, over `Z_R`, is

```
T = [1 0 1 1 2 1 4
     0 1 1 2 1 4 1].
```

Fix two differing encoded symbols `F`, and a nonempty set `S` of output coordinates. Choose `|S|` columns `J` from `F` giving a nonzero square minor `A=T[S,J]`. Condition on all other symbol keys. The chosen symbol NH differences are independent, and each specified value has probability at most `a`. Every solution of `A Delta = target (mod R)` therefore costs at most `a^|S|`.

The number of solutions to a soluble system equals its kernel size. Integer Smith normal form uses unimodular transformations, which stay invertible modulo `R`. For these matrices all relevant 2-adic valuations are below 64, so the kernel size is exactly `2^v2(det A)`. This is the sharper subset/minor method of the review; it does not use the invalid adjugate equivalence or Lemma 3's coordinate-independence assumption.

Define `c_S(F)` to be the smallest such kernel size. [encode2-minors.json](review-support/wrapper-cert/encode2-minors.json) gives the chosen columns, signed determinant, valuation, and kernel size for every nonempty row subset and all 21 choices of `F`. Exact enumeration proves

```
c_{0}(F) + c_{1}(F) <= 5,
c_{0,1}(F) <= 4.
```

Both maxima occur, for example, at `F={0,5}`: the singleton kernel sizes are 1 and 4, and the determinant is 4. The pair `{1,6}` also attains them. Every required minor is nonzero. Consequently, for any target vector and any selected coordinate subset,

`Pr[all selected leaf differences equal their targets] <= c_S(F) a^|S|`.

For a SIMD leaf, choose a physical lane in which the input differs. The encoder acts on that lane independently, even though keys are broadcast across lanes. Equality of whole output blocks implies equality on that lane, so the same subset bounds apply. No independence between lanes is asserted or needed.

## 5. Corrected k=2 core theorem

The statement here compares **equal byte lengths**. Let `n=floor(length/(144b))`, and for `n>=1` put `h=floor(log_8 n)`. The actual lazy forest may have smaller height, but never greater height.

If there are no complete leaves, the raw Toeplitz NH result of §3 gives core collision probability at most `a²=u`. If the two raw tails differ, condition on every EHC, tree, and forest-finalizer key. The tail target is then fixed, and the same Toeplitz result gives `u`, even if the forest contributions differ.

It remains to handle equal tails and at least one differing leaf. Select one such leaf and let `I_c` indicate equality of its entire output block in coordinate `c`. Conditional on all EHC keys, each coordinate's whole leaf sequence is fixed. If that sequence is nonidentical, its forest collides with probability at most `h a`. This follows by the usual level-by-level composition argument on a differing subtree, with fresh keys between levels. Key reuse at the same level does not add a factor equal to the number of nodes: equality of the whole output sequence is contained in equality at any one selected differing node. A remaining forest difference is compressed by fresh final NH keys with collision probability at most `a`. Lane sums are covered by conditioning on all but one differing lane's independent finalizer key.

Thus the conditional full-coordinate collision probability is at most `rho=(h+1)a` for a nonidentical coordinate sequence. Identical coordinate sequences imply `I_c=1`. The two coordinate tree/finalizer key sets are disjoint. Common raw tails cancel; their shared Toeplitz keys do not couple these coordinate collision events. Therefore

```
Pr[core collision]
 <= E[(rho+(1-rho)I_0)(rho+(1-rho)I_1)]
 <= rho² + 5a rho + 4a²
  = a² ((h+1)² + 5(h+1) + 4)
  = (h+2)(h+5) 2^-64.
```

Here `rho<1` on the entire certified domain. The subset bounds, rather than independence of `I_0` and `I_1`, justify the second inequality. This is a theorem for the **actual shipped Encode2** and actual key offsets.

For an integer word cap, define

```
B_b(L) = 2^-64                              if L < 18b,
         (h+2)(h+5) 2^-64                  otherwise,
h = floor(log_8(floor(L/(18b)))).
```

This bounds every equal-length distinct pair at that cap. Its score is 64: below a leaf the minimum is at `L=1`, and at the first leaf `18b/10>1`. Subsequent height-boundary lengths grow by eight while the coefficient grows by at most `18/10<8`. No larger length lowers the score. This statement is about the 16-byte core's collision bound, not a claim that its output is a uniform 128-bit value.

## 6. Tabulation with the overlap left in place

Write `C` for equality of the two complete core outputs, and `D` for the XOR difference of the two length-table outputs. Condition on **all words below 2048**. This fixes both core outputs and `D`, including every overlap. All output-byte table entries are still independent uniform words.

If `C` is false, select a differing byte in the two core signatures. At that byte position one of the two distinct table entries occurs exactly once in the XOR comparison; its row is distinct from every other byte row. Conditioning on all other output-table entries therefore gives **exactly** `u` collision probability, whatever the fixed value of `D` is. If `C` is true, all output-table terms cancel and a collision occurs exactly when `D=0`. Hence, without any independence assumption involving the core and length tables,

`Pr[H(m)=H(m')] = u Pr[not C] + Pr[C and D=0]`.    (1)

For equal lengths, `D=0` identically, so (1) is

`u + (1-u) Pr[C] <= u + (1-u)B_b(L) <= u+B_b(L)`.

For unequal lengths, the two length strings are distinct fixed eight-byte strings. The ordinary tabulation argument, applied **marginally**, gives `Pr[D=0]=u`. The core may depend on those exact entries; independence is unnecessary. Since `Pr[C]>=Pr[C and D=0]`, equation (1) gives

```
Pr[H(m)=H(m')]
 <= u + (1-u) Pr[C and D=0]
 <= u + (1-u) Pr[D=0]
  = 2u-u².
```

If the low 16 length bits differ, a fresh entry in rows 0 or 1 directly gives the sharper probability `u`; that observation is not needed for the general theorem. The argument also needs no unequal-length collision bound for the untagged core.

This settles the key-overlap issue on the stated domain. Conditioning on overlap alone does not magically make the length/core pair independent. Instead, equation (1) handles their dependence and uses only a valid marginal bound for `D`.

## 7. Wrapper bound, score, and a tight short example

Because `B_b(L)>=u`, both length cases satisfy

```
eps_b(L) = 2 * 2^-64                           if L < 18b,
           ((h+2)(h+5)+1) * 2^-64             otherwise.
```

All these values are below 1. The output floor changes none of them. At `L=1`, `log2(L/eps_b(L))=63`. The first leaf boundary is `64+log2(18b/11)>63`; later boundary lengths grow by eight whereas their coefficients increase by less than eight. Within each plateau the score increases. Thus

**`min_L log2(L/eps_b(L)) = 63` for each of the four wrappers.**

One can retain the `(1-u)` terms: `eps*_b(L)=u+(1-u)B_b(L)`. Its score is `64-log2(2-2^-64)`, slightly more than 63 (by about `3.91e-20` bits). This is not an asymptotic approximation to 64 bits.

Indeed take the equal-length one-byte messages `00` and `01`. There are no EHC leaves. In each of the two output coordinates, only physical lane zero differs, and its NH difference is `z` unless the low key half is `Q-1`, when it is `-(Q-1)z mod R`. It vanishes iff the corresponding high key half `z` is zero. The two relevant words are at absolute indices `659` and `659+b` and are independent, so core equality has probability exactly `u`. Length terms cancel and output tables are independent, hence the exact wrapper collision probability for this pair is

`u+(1-u)u = 2^-63 - 2^-128`.

This pair attains the sharp envelope at `L=1`. Thus the word-cap score of the actual flat-address family is exactly `64-log2(2-2^-64)`; **63** is its conservative integer certificate. This example is not an Encode2 defect or an overlap attack, and it is not described as a violation of the paper's long-input core theorem.

## 8. HalftimeHash24 is reachable and its advertised bound is refuted

There is no top-level function literally named `HalftimeHash24` in this header. Nevertheless the externally callable `halftime_hash::advanced::V1<3>`, `V2<3>`, `V3<3>`, and `V4<3>` are explicitly specialized public namespace functions. They write three `uint64_t`s, instantiate `(7,3,9,3)`, and reach `Encode3`. The ordinary Style wrappers all select width 2 and never call it. The real-header witness calls these width-3 entry points, not just `Encode3` in isolation.

### 8.1 The fixed pair

For each `b=1,2,4,8`, take messages of length **`168b` bytes**, exactly one width-3 leaf:

* `m`: all zero bytes;
* `m'`: the same bytes, except 64-bit word number **`6b`** (zero based) is the integer **1**; equivalently byte `48b` is `01` on the tested little-endian ABI.

For the paper's default block width `b=8`, this is a pair of **1,344-byte** messages differing at byte **384**. For scalar `b=1`, it is a pair of 168-byte messages differing at byte 48.

`Encode3` captures `iter=raw_io+1` by value in `DistributeRaw`. Every later distribution reads from that same address, regardless of the outer pointer's advances. Its initialization and parity writes therefore depend only on the first four raw blocks. Changing block 6 leaves both added symbols unchanged. Exactly encoded symbol 2 differs, in the first block of its triple and in physical lane zero. This proves minimum distance 1 (the systematic input symbols also prove it cannot be zero).

### 8.2 Exact key-fibre count for a full-hash collision event

Number keys relative to the advanced core pointer. Write

`core_key[6] = A + Q Z`, with `0<=A,Z<Q`.

The only changed symbol-NH product changes from `AZ` to `((A+1) mod Q)Z`. Its difference modulo `R` is

```
Delta = Z                  when A < Q-1,
        -(Q-1) Z mod R     when A = Q-1.
```

Both multipliers of `Z` are odd, so each is invertible modulo `R`. Among `0<=Z<Q`, **Delta is zero iff Z=0**. The changed symbol's combine column is `[1,0,1]`; therefore the entire EHC output is equal iff `Z=0`, for arbitrary values of every other key word. The other physical lanes are identical as well.

There are `(Q-1)*1 + 1*1 = Q` favourable choices of `(A,Z)` out of `Q²`. For a full key of `N` independent 64-bit words, this explicitly counts

`Q * R^(N-1)` keys out of `R^N`.

On every one of these keys, the full EHC vectors are equal. Every subsequent operation receives identical values and identical lengths: the forest is one leaf, and the extra raw block is zero in both calls. Thus **all three final output words are equal**, whatever the remaining key words are. Consequently

**`Pr[full 24-byte core collision] >= 2^-32`.**

This is an **exact count of a subset of the full collision fibre**, sufficient for a rigorous lower bound. It is not an assertion that the full collision probability equals `2^-32`; final-NH collisions can add other keys. No inference from observed collision frequencies is used.

At one leaf `h=0`. The supplied TeX's cumulative HalftimeHash24 expression, with determinant valuation 2 as used by the review, is `(64+0+1)2^-96 = 65*2^-96`. The counted lower bound exceeds it by `2^64/65`. The paper confuses a power of two with its exponent: even reading its printed `p=2²` literally inside `2^(kp)` would give `4097*2^-96`, still far below this witness. It also exceeds the looser textual “more than 83 bits” claim for these inputs. Appending the length cannot fix this witness because both lengths are the same. This is a **verified collision-probability counterexample**, beyond the earlier counterexample to the encoder assumption or Lemma 3.

### 8.3 Verification and remaining valid statements

[certificates.py](review-support/wrapper-cert/certificates.py) performs the integer gcd/fibre counts, records both branches, and checks the same identity exhaustively at smaller half-word widths. [header-check.cpp](review-support/wrapper-cert/header-check.cpp) includes the unchanged header, checks the exact EHC difference formula, and checks full output equality on the favourable fibres for all four block widths. Each build exercises 7,680 selected key-word/context cases per width, including low-half wrap and high-half boundary values. Of these, 1,280 per width belong to the favourable fibre. These counts are deterministic correctness checks, **not random-key collision-rate measurements**. Exact fibre counting is the requested alternative to a `2^28`-key experiment and is stronger here: that experiment would expect only 1/16 occurrence of the counted event.

Scalar, SSE2, AVX-512 and the disclosed NEON dispatch-alias build produce identical verification digests. Stock NEON cannot be run because it does not compile; no result is silently attributed to that nonexistent build.

The failed headline does not prevent a weak equal-length upper bound. Since `Encode3` is systematic, select one differing symbol and a lane. Every `Combine3` column has an odd entry, so whole-leaf collision costs at most `a`. Ordinary vector composition then gives `(h+2)a` once a leaf exists (one EHC, at most `h` tree levels, one final NH); differing tails give at most `a³`. Below a leaf the equal-length bound is `a³`. This has a conservative score `31+log2(21b)` (35.3923, 36.3923, 37.3923, 38.3923 bits for `b=1,2,4,8`) with the same sentinel-safe restriction, now `length<168b(C8+1)`. It is not the claimed 96-bit repaired-distance-3 result. For the untagged raw API across arbitrary unequal lengths, empty input versus one zero byte collides deterministically, so no positive all-length score follows. The paper explicitly treats its raw core as an equal-length family.

## 9. Literal source and platform qualifications

1. **Table type:** header lines 1018–1026 declare `const uint64_t (&table)[1+width][256]`. At width 2 the accesses `table[8]` and `table[16]` exceed the declared first dimension. A large caller allocation prevents a physical allocation overrun, but does not make those array subscripts valid ISO C++. The flat-address theorem uses exactly the addresses these expressions generate in the tested normal builds. UBSan diagnoses the declared-bound error. Consequently there is no portable-C++ certificate for the literal wrappers, even for very short messages, without a corrected table representation or an explicit implementation execution contract.
2. **Stock NEON:** lines 1124–1126 instantiate `V2Neon`, `V3Neon`, `V4Neon`; only `V2Sse2`, `V3Sse2`, `V4Sse2` were defined for the shared SSE2/NEON block type. Native Apple Clang rejects the unchanged include. The verification harness optionally aliases those three dispatch tokens to the existing functions. The header itself is unchanged; this is a disclosed build shim, not evidence of a successful unmodified NEON build.
3. **Signed lane sums:** the NEON `Sum(u128)` adds two values returned by `vgetq_lane_s64`; SSE/AVX horizontal helpers likewise use signed vector elements in scalar additions. Their intended arithmetic is modulo `2^64`. The SIMD verification builds use `-fwrapv`. The theorem assumes modular sums, not unconstrained signed-overflow optimization.
4. **Stack sentinel:** beyond the byte limits in §2, the actual header can read past `stack_lengths`. No collision bound is asserted beyond that domain. The safe-domain theorem does not repair the code or turn the public entropy allocation into a length check.

These limitations are kept separate from the cryptographic conclusions. There is a complete overlap-aware theorem for the shipped address-level algorithm, and an explicit counterexample to the width-3 core claim. A bounds diagnostic or a build failure is neither a probabilistic collision attack nor evidence that the stated address-level theorem is false.

## 10. Reproduction

See [review-support/wrapper-cert/README.md](review-support/wrapper-cert/README.md) for exact commands, the distinction between expected failures and passing checks, and the execution logs. Exact minor, layout, score, and fibre results are in [results.json](review-support/wrapper-cert/results.json). Computation on the Xeon used `nice -n 10` and one worker at a time; no wide random-key search was necessary. Local runs used no more than two computation threads. The source header was not edited.
