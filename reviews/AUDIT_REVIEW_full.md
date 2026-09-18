# Independent second reading of the hash-proof audit

Reviewed 2026-09-18. This review **closes VHASH's theorem-level gap**, certifies the **32-bit RFC UHASH collision bound**, gives a **rigorous numerical key-count bound for ideal Polymur**, and replaces the audit's very weak HalftimeHash repair with a bound retaining three powers of the NH error. It confirms invalid steps in the Polymur ASU and UMASH projection arguments and in HalftimeHash Lemma 3. **A counterexample to a proof step is not a counterexample to the claimed production collision bound.** No production collision attack on Polymur or UMASH is established here.

The ideal CLHASH, NH, tabulation, field-polynomial, recurrence, and ChainHash collision theorems survive this second reading. Several implementation claims in `AUDIT.md` refer to files absent from this workspace; they are not independently certified merely by repeating that audit or `provable.json`.

## Scope, conventions, and summary

I fetched the primary documents, read their relevant proofs, and separately checked the supplied TeX. Downloads and SHA-256 hashes are in [the source manifest](review-support/sources/MANIFEST.tsv). Computations are reproducible with [checks.py](review-support/checks.py); [results.json](review-support/results.json) records exact integer/rational quantities. One agent was used; network access was confined to retrieving primary papers, specifications, and their associated proof/reference files. No author was contacted.

Write `q=2^64`, `p=2^61−1`, and `clip(x)=min(1,x)`. Messages are fixed independently of the random key. Unless a section says otherwise, the random key is the **full specified independent random material**, not a short PRNG seed. AU concerns equality of the whole output. AXU concerns every fixed XOR difference; ADU concerns every fixed difference in the specified additive group. These properties are not interchangeable. Where no nontrivial implementation certificate is available, the universally valid fallback is `ε(L)=1`, scoring 0; a different explicit fallback is given for UMASH. This is a limit of the proof supplied here, not an estimated collision rate.

`L` is a positive integer number of 8-byte words. A byte-string cap means at most `8L` bytes; a fixed-length theorem instead compares two messages of that same length. The supplied paper explicitly floors the scoring error at `2^-r` for an `r`-bit output. To compare with its table, scores below use

`e(L)=max(2^-r, clip(ε(L)))`,  `bits=min_L log2(L/e(L))`.

This floor is a **score convention**, not a lower bound on actual collision probabilities. Section 9 gives the important unfloored alternatives. Except where stated, byte lengths are `<2^64`, so full-word caps can be taken through `M=2^61−1`. A score here is a score of the displayed rigorous upper bound, not an assertion that some message pair attains that bound.

Verdicts use the requested distinctions: **closed** means a complete argument is supplied; **confirmed** means the specified proof step is invalid or omitted and is not repaired to the advertised conclusion; **undecidable from the text** means the supplied specifications/proofs do not establish the particular implementation or joint-distribution claim. “Undecidable” is epistemic here, not computability-theoretic.

Abbreviations used in the table:

* `K0=189729088763903999`; `D` is the piecewise Polymur degree bound in §1.
* `H(L)=2^-96` for `L<168`; otherwise `H(L)=2^-96(h+2)^2(h+5)`, where `h=floor(log_8(floor(L/168)))`.
* `a=2^-32`, `b=2^-35+(2^54+6)/2^100+32(2^28+1)/2^64`, and `U_t=a+(1−a)b^t`.
* `V(L)=2^-62+1/(q−257)+ceil(L/16)/2^116`.
* `F_r(1)=2^-r/(1−561/q)`, `F_r(L)=1` for `L≥2`. This deliberately weak UMASH fallback is proved only from the short-string branch and the trivial probability bound. It is **not** evidence of a high actual collision rate.

| Family | Auditor verdict | Your verdict | Rigorous bound | Bits |
|---|---|---|---|---|
| CLHASH, ideal Algorithm 4 | Holds | Holds on `<2^64` bytes | `1/q` through 128 words; otherwise `2/q+(ceil(L/128)−1)/2^126` | 64 |
| CLNH, reduced / unreduced | Holds | Holds | `1/q` AXU, fixed padded length | 64; 65 if only unpadded even lengths |
| Polymur, ideal uniform-key AU | Correction; cardinality unverified | **Closed with corrected bound**, including numerical denominator | `D(8L)/\|K\| ≤ D(8L)/K0` | `log2(\|K\|/9)`; certified ≥54.2267934 |
| Polymur numerical headline / ASU | Unverified | **Confirmed proof gaps**; headline itself not disproved | Corrected AU above; arbitrary output-pair probability only trivially `≤1/q` with an independent uniform pad | AU as above; no certified ASU headline |
| Polymur shipped seed distribution | Unverified | **Undecidable from supplied proof** | `clip(D(8L) μmax)`, where `μmax=max_k Pr[k]`; absent a bound on it, `1` | No nontrivial certified score; trivial 0 |
| UMASH-64 | Projection gap | **Confirmed proof gap**; actual headline unsettled | Conditional formula in §2; explicit unconditional fallback `F_64` | No certified 55; fallback scores 1 |
| UMASH-128 | Same gap; global score wrong | **Confirmed proof gap and score-domain issue** | Conditional joint formula in §2; fallback `F_128` | No certified 83; fallback 1; claimed formula scores ≈68 on full byte domain |
| HalftimeHash24, abstract core | Strong bound unverified; repair 39.3923 bits | **Confirmed gap in Lemma 3; much stronger repair closed** | `clip(H(L))`, correct distance-3 encoder, independent stage/tree keys, equal lengths or length appended | **96** for this repaired envelope |
| HalftimeHash current `Encode3` | Distance assumption fails | **Confirmed by direct execution** | Abstract core using this systematic encoder: `(h+2)2^-32` once a leaf exists; `2^-96` below a leaf | 38.3923174 for that abstract model; no implementation certificate |
| HalftimeHash shipped 64-bit wrappers | Unverified | **Undecidable from paper; independent abstract wrapper repair in §3** | General wrapper: only trivial `1` certified here; independently keyed corrected variant described below | General: no nontrivial certificate; independent corrected variant: 63 |
| NH / standard two-word-shift Toeplitz NH | Holds | Holds | `2^-w` / `2^-wt`, equal lengths | NH32 32; NH64 64 with padding, 65 on pairs only |
| RFC UHASH-32, ideal hash equality | Advertised bound unverified | **Closed**: conservative component proof already suffices | `U_1 < 2^-30` | 30.3561156 for `U_1`; 30 for RFC envelope |
| RFC UHASH-64/-96/-128 | Advertised powers unverified | **Undecidable from checked texts**; conservative joint bound improved | `U_t`, `t=2,3,4` | `−log2 U_t`, just below 32; not certified 60/90/120 |
| VHASH-64, revised 2007 family | Holds with repair | **Closed**, with explicit unequal-length repair | `clip(V(L))`; also implies published `2^-62+1/(q−257)+ceil(L/16)2^-115` | 61.6780719 |
| VHASH with two fully independent keys | Qualified | **Closed** for independent copies | `V(L)^2` on `8L≤2^59` bytes | 123.3561438 |
| VMAC / shared-key multi-output implementation | Needs qualification | **Undecidable from transferred single-output theorem** | First-component VHASH equality bound under its ideal marginal; no squared bound certified here | 61.6780719 from that marginal; MAC game differs |
| Odd one-word multiply-shift | Holds | Holds; no theorem gap | `min(1,2^(1−r))`; zero if `r=w` | `r−1`; full 64-bit permutation scores 64 with floor |
| Vector / pair multiply-add-shift | Holds, benchmark caveats | Holds; **exercise completed** in §6 | `2^-r`, independent `W`-bit keys, `W≥w+r−1` | 64 for 64-bit output when `L=1` admitted |
| Named multiply-shift benchmark variants | Domain/key mismatch | **Undecidable for absent code; genuine generic failure modes verified** | Mathematical family above; no automatic transfer to cycling/seeded variants | No implementation certificate |
| Simple tabulation | Holds | Holds | `2^-r`, independent table entries, fixed positions | 64 for an admitted 8-byte key |
| Prime-field polynomial hashing | Encoding/output correction | **Closed with explicit domain** | `(d−1)/p0` fixed-length AU; `d/p0` positive-power ADU | Depends on packing; §9 |
| Horner over `GF(q)` | Holds | Holds | `(L−1)/q`, fixed length | 64 with floor |
| BRW | Raw/authenticator distinction | **Closed with that distinction** | `d_B(L)/q` raw, or published loose `(2L−1)/q` | Approximately 63; exact finite minima in §9 |
| Three-key recurrence | Holds | Holds; decoder checked independently | `ceil(L/2)/q`, fixed padded length | 64; 65 on even-only domain |
| Eight-lane recurrence | Holds for specified lanes | Holds for that explicitly defined family | `(ceil(ceil(L/2)/8)+7)/q` | 61 |
| Paper's 89-bit timed row | Code/theorem mismatch | **Undecidable as a measured-code claim**; ideal theorem valid | Three-key `ceil(L/2)/(2^89−1)`; two-key alternative in §10 | Conditional ideal ≈89 or ≈88 as specified; measured score unverified |
| ChainHash 1 KB / 256 B / 64 B | Holds, ideal key only | Holds; no collision-proof gap found | `(2ceil(L/128)+2)/q`; `(ceil(L/32)+2)/q`; `(ceil(L/8)+2)/q` | 62 / 62.4150375 / 62.4150375 |

## 1. PolymurHash 2.0

Primary sources: the fetched [README](https://github.com/orlp/polymur-hash/blob/master/README.md), [universality proof](https://github.com/orlp/polymur-hash/blob/master/extras/universality-proof.md), and [reference header](https://github.com/orlp/polymur-hash/blob/master/polymur-hash.h). Local copies are in `review-support/sources/polymur-*`.

### 1.1 The injective polynomial argument works over the field

Set `p=2^61−1` and

`K={k∈F_p*: ord(k)=p−1, canonical(k^7)<2^60−2^56}`.

For a nonfinal 49-byte block the seven nonconstant coefficients, in descending order, are

`m6+3, m0, m2, m4, m5, m3, m1`.

All recoverable data coefficients lie below `p`, and `m6+3` is nonzero modulo `p`. Multiplication by `k^7` separates the seven highest coefficients of successive blocks. Decode the earliest block from those coefficients, subtract its **entire** polynomial, including its constant term, and iterate. Then remove the `k^14` shift and decode the tail. For the largest tail, powers 11, 9, 6, 3 determine `m0,m6,m1,m2`; powers 7, 4, 2 determine `m3,m5,m4` after subtracting known products. Power 1 determines tail length. The smaller tails are immediate from the displayed formulas. Branch degrees 3, 9, 13, and prefix degrees at least 21 distinguish the branches. The byte-loading scheme covers the tail, so the length and decoded words recover the bytes.

Thus the map is injective **in `F_p[k]`**, not merely over the integers. Root counting is legitimate. For strings of at most `n` bytes, a safe sharper difference-degree bound is

```
D(n) = 2                              1 ≤ n ≤ 7
       9                              8 ≤ n ≤ 21
       13                             22 ≤ n ≤ 49
       7 floor((n−1)/49) + 14          n ≥ 50.
```

The common cubic cancels in the first range. Across tail branches, the higher branch's leading term need not cancel. This gives `Pr[collision]≤clip(D(n)/|K|)` for uniform `K`. A common output permutation and translation preserve equality. For a lazy representative, equality of representatives implies equality modulo `p`; the reverse implication is unnecessary. This algebraic statement assumes the implementation performs the described arithmetic without an unaccounted overflow.

**The dropped-constant gap is confirmed.** The source first proves `(14+n/7)/|K|`, then removes the positive 14 to state `n·2^-60.2`. The latter is not a consequence, particularly at short lengths. This does not prove the latter inequality false for the actual family.

### 1.2 Closing the cardinality gap with an explicit character-sum bound

The audit is right that the density estimate is not itself a proof. However, a rigorous estimate can be supplied without enumerating approximately `2^61` elements.

Put `N=p−1`, `m=N/7`, and `H=2^60−2^56−1`. The prime factorization is

`N=2·3²·5²·7·11·13·31·41·61·151·331·1321`.

In particular `7∤m`. Each element of order `m` has exactly six primitive seventh roots in `F_p*`: writing the roots' exponents modulo `N`, exactly one of the seven lifts is divisible by 7, and all seven are coprime to `m`. Consequently

`|K|=6 #{1≤x≤H : ord(x)=m}`.

For any nontrivial multiplicative character `χ` of `F_p`,

`|Σ_(x=1)^H χ(x)| ≤ sqrt(p) H_((p−1)/2) < 43·1518500250 = C`.

Here is a proof of the needed estimate. The nontrivial Gauss sums have absolute value `sqrt(p)`: expanding the squared norm, putting `x=ty`, and summing the additive character over `y≠0` gives `p`. Fourier inversion expresses the interval character sum as `1/p` times these Gauss sums times interval exponential sums. For a frequency at distance `r` from 0 modulo `p`, the geometric-series bound is `p/(2r)` because `sin(πr/p)≥2r/p` for `r≤p/2`. Sum the two symmetric frequencies to obtain `sqrt(p) Σ_(r=1)^((p−1)/2) 1/r`. Finally `sqrt(p)<1518500250` and `1+ln((p−1)/2)<43`. These are deliberately loose rigorous inequalities.

The indicator of the subgroup of order `m/d` is the average of the `7d` multiplicative characters trivial on that subgroup. Its interval count therefore differs from `H/(7d)` by less than `C`. Möbius inversion gives

`#{x≤H:ord(x)=m} = Σ_(d|m) μ(d) #{x≤H:x^(m/d)=1}`.

There are `2^11=2048` squarefree divisors of `m`, and `φ(m)=67744512000000000`. Therefore

`|K| ≥ 6Hφ(m)/N − 6·2048·C`.

Taking the floor of the main term gives the explicit integer lower bound

**`|K| ≥ K0 = 189729088763903999`.**

All factorization products and arithmetic are recorded in the executable check; an exact Lucas–Lehmer test also verifies the Mersenne prime used here. This closes the numerical-denominator issue **for a key sampled uniformly from this exact set**. It does not validate the deterministic initializer's distribution.

For integer-word caps, `D(8)=9`. For `L≥2`, `D(8L)≤14+8L/7≤9L`, so the minimum for the bound `D(8L)/|K|` is at `L=1` and equals `log2(|K|/9)`. The certified numerical score from `K0` is `log2(K0/9)=54.2267934975…`. Clipping and the 64-bit output floor cannot lower that minimum.

### 1.3 The seeded distribution and ASU argument remain separate gaps

The initializer adds a fixed odd constant repeatedly to the seed and accepts the first admissible exponent/key. This is a walk through a finite permutation cycle, **not independent rejection sampling**. A successful state receives every seed in its preceding rejection run. Even if the initial seed is uniform, accepted states need not be uniform; exponent extraction introduces its own multiplicities. The code defines a finite distribution, but the supplied proof gives no bound on its maximum atom `μmax`. Root counting under that distribution yields `D(n) μmax`, not `D(n)/|K|`. The one-seed initializer also does not make its two derived secrets independent.

For the two-secret ideal model, an independent uniform `s∈Z_q` gives exactly

`Pr[H(m)=x,H(m')=y] = q^-1 Pr_k[mix(P_m(k))−mix(P_m'(k))=x−y mod q]`.

For `x=y`, AU bounds the right side. For arbitrary `x−y`, a new **additive differential bound after the nonlinear mixer** is needed. The proof fixes `s` to count roots and then selects a different `s` for each `k`; the root polynomial changes with that selection. Also, its expression solving for `s` has the sign reversed.

A complete counterexample to this counting implication is over `F_5`: take `f(k)=k`, `g(k)=2k`, and the permutation with values `[4,0,1,3,2]`. Add an independent uniform pad. Output pair `(0,1)` occurs at `(k,s)=(1,0),(2,4),(4,3)`, hence with probability `3/25`. Every fixed-pad equation `f−g−constant=0` has at most one root. It is therefore false that this reasoning limits all simultaneous solutions to one. This is a proof-step counterexample, not a counterexample using Polymur's actual mixer.

**Verdicts:** ideal AU/cardinality **closed with corrected argument**; deleted constant and ASU root counting **gap confirmed**; shipped seed bound **undecidable from supplied proof**.

**Proposed author note:**

> Thank you for publishing the polynomial encoding and proof. I can verify field-level injectivity and the bound `(14+n/7)/|K|`; a sharper piecewise degree bound and an explicit character-sum estimate give an ideal uniform-key score of at least 54.2267 bits. I cannot derive the stated short-message headline after dropping 14. In the almost-pairwise-independence argument, the fixed-pad root polynomial changes when the pad is subsequently chosen as a function of the key. Could you supply a differential bound for the mixed polynomial outputs, and a maximum-atom or uniformity argument for the actual initializer? These are distinct from the verified ideal AU statement; I have not found a collision attack on the implementation.

## 2. UMASH-64 and UMASH-128

Primary sources: the fetched [whitepaper](https://github.com/backtrace-labs/umash/blob/master/umash.pdf), dated 2022-02-23, and its [literate reference source](https://github.com/backtrace-labs/umash/blob/master/umash_reference.py). The disputed projection sentence is on PDF p.6, reference lines 366–381; the corresponding fingerprint step is on lines 744–770. I checked the PDF rendering against the extracted text.

### 2.1 What is actually proved before projection

For the first compressor, PH is full-width carryless NH. Subtracting two PH values with XOR cancels the key-key product; conditioning on one key leaves a nonzero polynomial times the other key. Multiplication is injective in `F_2[X]`, hence every fixed XOR difference has probability at most `1/q`.

Unsigned NH is `1/q`-ADU modulo `q²` (proved in §4). Adding the block tag gives ENH: different data use that differential theorem; identical data with different tags cannot collide before projection.

For equal chunk counts in OH, choose a differing PH chunk if one exists and condition on all other chunks; PH's AXU bound handles the XOR of all remaining contributions. If no PH chunk differs, only the ENH comparison remains. The raw OH equality bound is therefore `1/q`. For unequal counts, the longer message's final ENH key pair is fresh relative to the shorter message. For independent uniform `A,B∈[0,q)`, any nonzero integer product value has at most `q−1` preimages, while zero has `2q−1`. Thus any prescribed final ENH value has probability at most `(2q−1)/q²<2/q`, giving the raw all-length bound.

The raw 128-bit fingerprint analysis can also be justified. If checksum chunks differ, fresh checksum-PH keys give a conditional `1/q` factor. Unequal counts have checksum equality probability `1/q²`; otherwise multiply the primary bound by `1/q`. For equal counts and equal checksums, a tag-only difference cannot collide in the primary raw output. A genuine data difference then affects at least two chunks. With one PH and the ENH chunk differing, simultaneous raw equalities force `(I+s_j)Δ_PH=0`; this map is invertible since it is identity plus nilpotent left shifts. Both independent chunk differences must vanish, costing at most `q^-2`. With two PH chunks differing, eliminate one of the two equations. The other is restricted to a shuffler-kernel coset with at most `2^29` possible PH differences; PH's top output bit is zero. Each specified difference costs `q^-1`, and the independent other PH difference costs another `q^-1`. This proves the loose raw bound `2^29/q²=2^-99`. Shared completed hashes have not been assumed independent.

### 2.2 The projection inference does not follow

The paper then maps both 64-bit halves to `F_p` and estimates the effect as losing about six bits; for the fingerprint it maps four halves and subtracts about twelve bits. An AU collision bound is a bound on a diagonal event, not a bound on the mass of every output pair. A projection can move off-diagonal mass onto that diagonal. Even AXU does not justify projection to an unrelated additive group.

Here is the audit's generic witness independently verified. For five equally likely keys let `u∈{1,2,4,8,16}`, with 6-bit outputs `H(x)=u`, `H(y)=u+31`. The five XOR differences are `33,35,39,47,63`, all distinct, so this two-message family is `1/5`-AXU. Reducing modulo 31 makes the two outputs equal for **every key**. The largest projection fibre has size 3, so the proposed fibre-times-AXU implication would give the false upper bound `3/5`.

For actual UMASH, each half has at most **nine** representatives of a residue modulo `2^61−1`. Replacing 8 by 9 in an entropy calculation does not repair the inference. I tried the natural lifts: an integer-ADU bound could handle congruence lifts, but OH XORs PH and ENH and is not shown integer-ADU; a PH AXU bound handles fixed XOR targets, but modular congruence after a common XOR mask does not specify a fixed XOR target. In the fingerprint proof, the raw-zero equations used in the PH/ENH case likewise do not provide all the projected differential equations. None of these routes closes the published step.

### 2.3 An exact statement of the missing lemma and the bound it would imply

Condition on the OH parameters. For a long/long comparison, form the **formal polynomial difference after reducing all coefficients modulo `p`**. For a long/short comparison, subtract the short result after undoing the long output permutation and reducing modulo `p`. This is a constant independent of the polynomial multiplier, even though it can depend on OH keys. Let `B_1(s)` be an upper bound on the probability that this comparison polynomial is identically zero. This definition includes unequal block counts and vanished leading coefficients; bounding only equal-length block-vector collisions is insufficient.

The long finalizer is invertible: for the bit-rotation operator `R`, `I+R^8+R^33` is coprime to `R^64−I=(R+I)^64`, since its polynomial equals 1 at `R=1`. Thus undoing it in the preceding comparison is legitimate.

The multiplier is uniform on the actual reference set `F_p\{0,1}`, of size `p−2`. With `d=2 ceil(s/256)` and `r_s=min(1,d/(p−2))`, the rigorous conditional completion is

`Pr[UMASH64 collision] ≤ B_1(s)+(1−B_1(s)) r_s`.

For two components, let `B_2` bound the secondary zero-polynomial event and `B_12` their joint occurrence. Independent polynomial keys then give the safe bound

`Pr[fingerprint collision] ≤ B_12+(B_1+B_2)r_s+r_s²`.

This follows by partitioning into both comparison polynomials zero, exactly one zero, and neither zero. It does not assume independent compressors. The missing result is a sufficiently strong **single and joint projected-polynomial identity bound**, including length and short/long cases. The raw `2^-63` and `2^-99` estimates do not establish those quantities. The loose arithmetic in the final rounding is not a substitute for this lemma.

The reference OH key generator samples 34 distinct words. A correct IID proof could be transferred by conditioning, paying at most the factor `1/(1−binom(34,2)/q)=1/(1−561/q)`. This tiny correction is repairable once the main proof is supplied. The missing projection lemma is not repaired by it. A stream-cipher expansion gives a computational interpretation, rather than full information-theoretic key independence.

### 2.4 Bounds and scores we can and cannot certify

For IID keys, two distinct strings of the same length at most eight bytes never collide. Different short lengths collide with probability `q^-1` for the primary. For the fingerprint, two distinct shifted key-pair constraints form a forest, even if they share one key word; expose a root and then the remaining endpoints to obtain `q^-2`. Conditioning on distinct OH words yields the upper bounds `q^-1/(1−561/q)` and `q^-2/(1−561/q)`.

Thus the explicit all-domain fallbacks `F_64` and `F_128` in the table are rigorous: use these short-string estimates at `L=1`, and probability at most 1 at every `L≥2`. Their minimum score is **1 at `L=2`**. This intentionally weak certificate conveys the limit of this review's completed proof; it must not be described as an attack or the measured strength of UMASH. No nontrivial all-length replacement for the published headlines is established here.

As arithmetic on the **unverified** claims, UMASH-64 scores 55 at `L=1`. For UMASH-128, put `A=2^23` words and `j=ceil(L/A)`. On a plateau, minimize at its first integer length. The relevant candidates are `L=1` and `L=(j−1)A+1`; their score is `83+log2 L−2log2 j`. With `L≤2^61−1`, the last plateau starts at

`L*=2^61−2^23+1`, `j=2^38`,

giving **`7+log2 L*`**, slightly below 68. On the range through 64 MiB the conditional score is 83; 83 also persists on some larger capped domains, so 64 MiB is a sufficient cap, not a uniquely necessary cutoff. The audit's full-domain correction is right.

**Verdict for both widths: gap confirmed in the published argument; the advertised numerical collision bounds remain unsettled, not disproved.**

**Proposed author note:**

> I can reproduce the raw OH bound and the fingerprint's `2^-99` raw joint bound. The step on p.6 that reduces each half modulo `2^61−1` appears to need an additional lemma: AU, and even AXU alone, do not bound the collision increase under this projection. Could you provide the single and joint bounds for the resulting formal coefficient polynomials, including unequal block counts and short/long comparisons? With those in hand, the independent polynomial-key root counts can be completed directly. I have not found a UMASH counterexample to the advertised bounds. Separately, the 128-bit formula gives a length-normalized score near 68 on the full 64-bit byte-length domain; an 83-bit table entry should state its length cap.

## 3. HalftimeHash

Primary sources: [arXiv:2104.08865v2](https://arxiv.org/pdf/2104.08865), especially Theorem 1, Lemma 3, and §6.2; the fetched [reference header](https://github.com/jbapple/HalftimeHash/blob/main/halftime-hash.hpp). The correct arXiv number is 2104.08865. The paper's HalftimeHash24 has a 24-byte core output; the public `Style64/128/256/512` names describe implementation styles, whose wrappers all return 64 bits.

### 3.1 What is wrong, and what a repair must track

The generalized EHC proof uses `p` both as a power of two and as its exponent. Interpreting it as the maximum **valuation** `a=v2(det A)` repairs that notation. After multiplication by an adjugate, equivalence must sometimes be replaced by implication; dividing `2^a Δ=β` also requires dividing `β` when it is divisible by `2^a`. The audit correctly repairs this argument to `2^(ka) ε^k` with `ε=2^-32`.

Lemma 3 on PDF p.9 has a more substantial problem. Noncollision of a `k`-component EHC vector does not ensure that each component differs. For example, vectors `(0,0)` and `(1,0)` are distinct. The second coordinate tree receives identical strings and collides with probability 1, regardless of its independent key. With affine universal maps over `F_4` for the two coordinate trees, the joint collision probability is `1/4`, not `(1/4)^2`. Thus the lemma's conditional multiplication is false as a general implication. This witness alone does not disprove the final bound for the actual EHC distribution.

The audit's replacement treats this as an ordinary vector-composition problem and loses two powers of `ε`. That is safe for the stated abstract model but unnecessarily pessimistic. EHC supplies **joint bounds on every subset of output coordinates**, which retain the missing powers.

### 3.2 A sharper EHC lemma

Suppose the code has distance 3. Choose three differing encoded symbols `F`. For the displayed `3×9` combine matrix

```
T = [0 0 1 4 1 1 2 2 1
     1 1 0 0 1 4 1 2 2
     1 4 1 1 0 0 2 1 2],
```

fix a subset `S` of `r` output rows. Choose `r` columns `J⊆F` with nonsingular minor `A=T[S,J]`, condition on all other symbol-hash keys, and write the selected NH differences as `Δ`. Every vector value of these independent differences has probability at most `ε^r`.

The equation `AΔ=c` over `Z_(2^64)` has at most `2^v2(det A)` solutions, not the much looser `2^(r v2(det A))` delivered by the adjugate bound. To see this, use integer Smith normal form. Its two unimodular changes of coordinates remain invertible modulo `2^64`. A diagonal entry with valuation `e` has `2^e` kernel elements here; the sum of the valuations is `v2(det A)≤2`. Thus a soluble equation has a coset of that kernel as its solution set. Consequently

`Pr[all output differences in S equal prescribed targets] ≤ c_S(F) ε^r`,

where `c_S(F)=2^min_(J⊆F, |J|=r) v2(det T[S,J])`.

All 84 choices of `F` have nonzero full determinant with valuation at most 2. Exact minor enumeration gives

`Σ_(|S|=1) c_S(F)≤6`, `Σ_(|S|=2) c_S(F)≤9`, `c_{1,2,3}(F)≤4`.

These are finite integer verifications, not sampled determinants: [all 84 certificates](review-support/halftime-minors.json) and their generating code are supplied. For example `F={0,1,3}` attains all three upper bounds. A looser proof using any minor of valuation at most 2 also works, with constants 12,12,4; it already suffices to recover a 96-bit score.

In the SIMD interpretation, select a physical lane in which the original leaf differs. The systematic XOR encoder acts separately on that lane. Equality of any subset of complete output blocks implies the corresponding equalities on the selected lane, so the same bounds apply even when NH keys are broadcast across SIMD lanes.

### 3.3 Completing the tree and final-NH argument

Fix equal-length distinct inputs with identical raw tails and choose one differing EHC leaf. Let `I_j` indicate equality of coordinate `j` at that leaf. If the entire input sequence to tree `j` is identical, then `I_j=1`. Conditional on the EHC keys, a nonidentical coordinate sequence collides through its tree and the final NH with probability at most

`ρ=(h+1)ε`.

This is ordinary independent composition: at most `hε` for a completed-tree/forest comparison, then `ε` for the final NH. The coordinate tree/final-NH key sets are independent. Therefore the full collision probability is bounded by

```
E [ product_(j=1)^3 (ρ+(1−ρ) I_j) ]
 ≤ ρ³ + 6ερ² + 9ε²ρ + 4ε³
 = ε³ ((h+1)³ + 6(h+1)² + 9(h+1) + 4)
 = ε³ (h+2)²(h+5).
```

The first inequality uses the subset bounds just proved, not independence of the `I_j`. On the byte-length domain under discussion `ρ<1`; one can clip it for larger domains.

If the raw tails differ, their fresh Toeplitz-NH keys bound the three-component difference at any prescribed target by `ε³`, after conditioning on the tree contribution. This is no larger than the displayed bound. If there are no complete EHC leaves, the whole input is such a tail and the bound is just `ε³`.

For the paper's `b=8,d=7,w=3` parameters, a leaf occupies `168` 64-bit words. With `h=floor(log_8(floor(L/168)))` for `L≥168`, this proves the function `H(L)` in the table. Unequal lengths can be separated by **appending the length to the core output**, as the paper specifies; that statement does not automatically certify its fixed-width public wrapper.

The score is **96 at `L=1`**. Below 168 words, it is `96+log2 L`. The first leaf boundary has score `96+log2(168/20)=99.0703893…`. Later height-boundary lengths grow by 8, whereas `(h+2)^2(h+5)` increases by a factor at most `54/20<8`; within each plateau the score increases. Thus no later length lowers the score. This improves the audit's conservative 39.3923-bit certificate without restoring the paper's particular `2^-96(64+h³+1)` formula.

### 3.4 Encoder and wrapper qualifications, checked against the source

The current `Encode3` does fail its distance assumption. `DistributeRaw` captures `iter` by value; later changes to the outer pointer do not affect its reads. Pointer advances are also by individual blocks, rather than three-block rows. I compiled the fetched header using its scalar path and called the function on two zero arrays differing only at `raw_io[6]`. Only encoded symbol 2 differs: symbol distance **1**, not 3. See [the witness](review-support/halftime-check.cpp) and [execution log](review-support/halftime-check.log). The scalar build was selected with `-U__ARM_NEON -U__ARM_NEON__`; this test makes no claim about NEON compilation or full-hash correctness. Public wrappers instantiate `Encode2`, so this is not an attack on those wrappers.

Even this defective encoder permits a weak **abstract-model** certificate: it keeps the data symbols unchanged, so some encoded symbol differs, and every column of the printed matrix has an odd entry. Select such an entry, condition on the other symbol keys, and invert its odd coefficient modulo `2^64`; EHC-vector collision is at most `ε=2^-32`. Treating the coordinate trees jointly then costs at most `hε`, and final NH at most another `ε`. The model bound is `(h+2)2^-32` above one 168-word leaf, and `2^-96` below it, scoring `31+log2 168=38.3923174…` at `L=168`. This bounds the mathematical composition with that systematic encoder; it does not certify the entire C++ implementation or repair the distance-3 claim.

There is also a fully explicit valid abstract distance-3 encoder with the apparent intended transforms. Keep seven three-component data symbols `x_i`, append `P=Σx_i`, and append `Q=ΣA_i x_i`. Over `F_2`, the seven `3×3` matrices have columns encoded as three-bit integers:

`[1,2,4], [4,5,2], [5,7,6], [2,6,5], [3,4,1], [6,3,7], [7,1,3]`.

Each `A_i` and each `A_i+A_j` for `i≠j` has rank 3, as verified by 28 complete binary eliminations in the check script. One changed data symbol changes itself, `P`, and `Q`. For two changed symbols, either `P` changes or their differences agree, in which case `(A_i+A_j)` makes `Q` change. Three or more changed data symbols already suffice. This proves distance 3 and gives a concrete encoder for the repaired **abstract** theorem. It does not declare the fetched function corrected.

For `TabulateAfter`, the audit's address calculation is correct: the core starts at word 512 for width 2, while the logical length/output tabulation region occupies words 0–6143. Its declared `table[3][256]` view also does not justify accesses to later rows. The independent-composition proof for the unrestricted wrapper therefore cannot simply be assumed. A finite stack needs a domain limit as well.

However, overlap alone does not prove a collision or invalidate every restricted use. For equal lengths, the length-table term cancels. Moreover the first two length-byte tables precede the core's starting address, so unequal lengths with different low 16 bits can be separated with a fresh length-table entry, in a flat-array mathematical interpretation. These are reasons to seek a restricted wrapper proof rather than announce that overlap itself breaks the bound. I do not certify the unrestricted C++ wrapper from those observations.

For comparison, an **independently keyed simple-tabulation wrapper** of the corrected abstract distance-2 core, including the length in the tabulated signature, does have a complete bound. The corresponding `2×7` matrix gives subset constants 5 and 4 by the same minor method. Its core bound is `2^-64` below one leaf and `(h+2)(h+5)2^-64` thereafter. Independent tabulation adds at most `2^-64`. With at least 18 input words per leaf, the loose resulting envelope has score **63**, attained at `L=1`. This is a repaired construction, not a proof of the shipped all-length wrapper.

**Verdicts:** Lemma 3's conditional step and the current distance-3 code failure are **confirmed gaps**; a substantially stronger abstract replacement is **closed with argument**; the shipped unrestricted wrapper bound is **undecidable from the checked paper/code argument**.

**Proposed author note:**

> In Lemma 3, EHC-vector noncollision appears insufficient to multiply all coordinate-tree collision bounds: some coordinates can agree. I can retain the intended three powers of the NH error by tracking every subset of equal EHC coordinates. For the printed 3×9 matrix this gives `2^-96(h+2)^2(h+5)`, including final NH, and `2^-96` below one leaf. The proof uses exact minor counts and a kernel-size bound. Could you check whether this supplies the intended correction? Separately, the fetched `Encode3` maps a change at `raw_io[6]` to only one differing encoded symbol; its captured pointer appears responsible. I have kept this distinct from the width-2 public wrappers and from the abstract theorem.
>
> For those wrappers, could you specify the supported length domain and the argument accommodating overlap between the core keys and the length/output tables? Independent tabulation composition does not directly apply to that layout. I have not established a collision counterexample from the overlap alone.

## 4. NH, Toeplitz NH, and standardized UHASH

Primary sources: [Black et al., UMAC full paper](https://web.cs.ucdavis.edu/~rogaway/papers/umac-full.pdf), Theorems 4.2 and 5.1 and §7; [Krovetz's dissertation](https://web.cs.ucdavis.edu/~rogaway/umac/umac_thesis.pdf), Chapter 6; [RFC 4418](https://www.rfc-editor.org/rfc/rfc4418.txt), §§5–6. The old `fastcrypto.org/umac/umac-full.pdf` URL returned 404; the author's university copy was successfully fetched. I checked the actual later layers instead of treating these versions as identical.

### 4.1 The NH theorem and standard Toeplitz theorem hold

Let `Q=2^w`. NH sums products of two operands reduced modulo `Q`, with the product/sum modulo `Q²`. In a differing pair, condition on its second key word, so the two second factors `c,c'∈[0,Q)` are distinct; condition also on all other pairs. Translate the remaining key `k` so the first message's operand is `k`. The comparison at any fixed additive target is

`c k − c' ((k+d) mod Q) = v mod Q²`, `0≤k<Q`.

Within each of the two intervals separated by the wrap of `k+d`, the slope is `c−c'≠0`. Two solutions in one interval would give a nonzero multiple of `Q²` of absolute value less than `Q²`, impossible. For solutions `k1` before and `k2` after the wrap, subtraction gives

`(c−c')(k2−k1)+Qc' = 0 mod Q²`.

If `c≥c'`, the left side is strictly positive and less than `Q²` (the zero case is excluded by `c≠c'`); if `c<c'`, it lies strictly between 0 and `Q²` as well, because `(c'−c)(k2−k1)<Qc'`. Thus there cannot be two solutions across the wrap. At most one of the `Q` keys works. This proves the full **ADU** bound, not just equality.

For standard Toeplitz NH with an even two-word key shift, truncate common suffix pairs and select the last differing pair. The next repetition has two fresh key words beyond those used by preceding comparison equations. Fix one and use the one-solution argument on the other. The conditional probabilities multiply to `Q^-t`. More generally, a shift by a whole number of such pairs works. The output is `2wt` bits. Signed NH has the different `2/Q` bound and must not silently replace the unsigned family.

Unmodified NH does **not** satisfy the same bound at unequal pair counts. Comparing a zero pair with two zero pairs leaves one independent extra product. It vanishes with probability `2/Q−1/Q²>1/Q`; at `Q=4` this is `7/16`. That refutes the sentence in the VHASH note, not either original equal-length NH theorem.

NH32's minimum input pair occupies one 8-byte word, giving score 32. NH64 starts at two words and gives 65; admitting one data word padded to a pair at a fixed length gives 64. These padding statements do not constitute a variable-length encoding theorem.

### 4.2 Directly certifying one RFC UHASH component

Use ideal independent KDF bytes for distinct stage keys. The following is a complete conservative AU argument for the **exact RFC stages**.

1. **L1.** At equal padded pair counts, different contents use NH's ADU theorem after the actual bit-length tags are added. If contents agree but lengths differ, the nonzero tag separates them. For unequal padded counts, start with the common-prefix difference and the nonzero length target. Its target probability is 0 if prefixes agree, otherwise at most `a=2^-32`. Add each independent extra product. For a nonzero first factor, at most one second factor hits any fixed target modulo `Q²`; for first factor zero, the prior event remains. Thus `p_new≤(1−1/Q)/Q+p_old/Q≤1/Q`. This proves L1-vector AU at most `a`; different chunk counts give vectors of different lengths. Striding is a permutation for this **single-output** result.
2. **L2 encoding.** RFC POLY starts at 1. A large word is replaced by the marker `p0−1` and its shifted payload; the marker cannot occur as an unescaped word. Parsing is unique, including when a payload itself equals the marker. The leading 1 distinguishes encoded lengths. Each source word supplies at most two field coefficients.
3. **L2 roots.** The 64-bit multiplier mask leaves exactly 50 random bits. At most `2^14` source words reach that layer, hence degree at most `2^15` and error `2^-35`. The 128-bit multiplier has 100 random bits. For original byte length `<2^64`, L1 output has at most `2^57` bytes; the long L2 input, including the prefix digest and terminator padding, has at most `2^53+3` 128-bit words. Degree at most `2^54+6` gives error `(2^54+6)/2^100`. Prefix-digest equality is paid for by the first term. Distinct suffixes remain distinct by the terminator and escape encoding. Cross-branch comparisons are a nonconstant monic polynomial minus a fixed short result, so are covered too. Uniformity over these restricted multiplier sets, rather than the whole fields, is the relevant denominator.
4. **L3.** The eight 16-bit input coordinates embed injectively in `F_(2^36−5)`. Distinct input vectors give a nonzero coefficient in their linear difference. A key coefficient is a uniform 64-bit integer reduced modulo that prime, so every field value has mass at most `(2^28+1)/2^64`. Conditioning on the other keys bounds each fixed field difference by that quantity. Equality after taking low 32 bits requires the canonical residues' integer difference to be a multiple of `2^32`. There are 31 possible multiples in the permitted interval; using 32 is safe. The final XOR pad preserves equality.

Independent composition therefore gives a post-L1 bound

`b=2^-35+(2^54+6)/2^100+32(2^28+1)/2^64`,

and overall `U_1=a+(1−a)b`. In particular `U_1<2^-30`.

**This closes the RFC's 32-bit collision headline.** The audit's own slightly looser `E_U=a+b≈2^-30.3561` already suffices; its blanket “advertised standardized bound unverified” is too broad for hash equality at `t=1`. The bound is length-independent, so its score is `−log2 U_1=30.3561156296…`, minimized at `L=1`. The RFC's looser `2^-30` envelope scores exactly 30. This is a hash-equality certificate, not a new proof of the full adaptive MAC-forgery game.

### 4.3 A joint bound that needs no unproved power of the L1 bound

For `t=2,3,4`, the later-layer keys of the RFC iterations are independent, although L1 keys overlap. Given all L1 key material, let `C_i` be the event that the two L1 vectors in iteration `i` are equal. Conditional full-output collision probability is at most

`product_i [ b+(1−b) 1_(C_i) ]`.

Every nonempty intersection of the `C_i` is contained in any one of them, hence has probability at most `a`. Expand the product and average:

`Pr[collision] ≤ b^t + a(1−b^t) = U_t`.

This rigorously improves using the first finished component alone. It scores `−log2 U_t` at `L=1`: about `31.99999999848` for `t=2`, and strictly below but extremely close to 32 for `t=3,4`. It does not establish the RFC's 60/90/120-bit envelopes.

A sufficient stronger missing statement would be `Pr[∩_(i∈S) C_i]≤a^|S|` for every subset of RFC iterations, including its length tags and different padded counts. The same expansion would then give `[a+(1−a)b]^t < 2^-30t`.

The original paper proves the standard whole-pair Toeplitz theorem and discusses striding and larger shifts separately. The RFC uses stride 4 on 32-bit words but a shift of **four** key words between iterations. A permutation preserving a single NH output does not by itself prove that the entire overlapping multi-output key layout becomes the theorem's whole-pair-shift layout. The dissertation's joint proof is useful for its own specified variant, but its parameters, signedness, and polynomial-layer organization differ. I do not find in these checked texts a fully spelled-out argument covering all these changes and the unequal-length joint events. Tiny checks of one-word-shift NH found no counterexample; those checks neither establish the production theorem nor justify accusing it of being false.

**Verdicts:** NH and standard Toeplitz NH **hold**; ideal RFC UHASH-32 equality **gap closed**; the specific multi-component RFC powers are **undecidable from the checked texts**, with the rigorous alternative `U_t` supplied. This is a narrower conclusion than a claim of a broken UMAC theorem.

**Proposed author note:**

> I can directly verify the RFC's 32-bit hash-collision envelope using its exact three layers. For the longer outputs, could you identify the joint L1 lemma covering the RFC's four-word key shifts, stride-four pairings, length tags, and unequal padded counts? A bound on every subset of L1-vector collision events would complete the independent later-layer composition. The 1999 and dissertation proofs establish closely related variants, but I have not completed this transfer. I have no counterexample to the RFC's 60/90/120-bit claims and would describe this as an unresolved proof-reference/transfer question.

## 5. VHASH and VMAC

Primary sources: [Krovetz, Message authentication on 64-bit architectures (2006)](https://krovetz.net/csus/papers/vmac.pdf); [Dai–Krovetz, VHASH Security, 2007/338](https://eprint.iacr.org/2007/338.pdf), Figure 1, Theorem 1, and §§1.1–1.2; [the VMAC draft](https://www.ietf.org/archive/id/draft-krovetz-vmac-01.txt). The 2007 note explicitly revises the earlier construction. Its larger final prime and different polynomial must be used together.

### 5.1 Repairing the false unequal-length NH sentence

The note's §1.1 says that the equal-length NH bound extends to arbitrary pair counts with small proof changes. The zero-extension example in §4 disproves that assertion as written. However, VHASH immediately reduces NH modulo `Q²/4`, with `Q=2^64`; it only needs the looser `4/Q` bound there.

For equal lengths, reduction modulo a divisor collects exactly four additive difference residues. Hence the bound is `4/Q=2^-62`.

For unequal pair counts, condition on every key except one extra product in the longer message. Count `AB=c mod Q²/4` with `0≤A,B<Q`:

* If `c≠0`, `A=0` supplies no solutions. Every nonzero `A≠Q/2` gives period at least `Q` for `B`, hence at most one solution. `A=Q/2` gives at most two. Thus there are at most `Q` solutions.
* If `c=0`, the zero rows/columns contribute `2Q−1` solutions. The only nonzero pair with sufficient combined 2-adic valuation is `A=B=Q/2`, giving exactly `2Q` total.

The maximum point mass is therefore `2/Q≤4/Q`. Any conditioned target offset is allowed. This proves the truncated unequal-count fact actually required by the algorithm. The exact counts are independently enumerated at word sizes 2, 3, and 4 in the support script.

### 5.2 Completing the polynomial and final stage

Let `P=2^127−1`, `r=q−257`, and `N=ceil(L/16)` for 128-byte blocks. The source's polynomial is

`k^n+a1 k^(n−1)+…+an+last_bitlength·q mod P`,

where every `ai<2^126`, and `k` is uniform on a set of **exactly `2^116`** points (four independently chosen 29-bit limbs). Different block counts give different monic degrees, so their formal difference is nonzero for every NH key. At equal counts, a differing nonlast block gives a nonzero coefficient except with probability at most `2^-62`. If only the last block or length differs, the equation for its coefficient fixes at most one integer difference of the `ai`, since their difference interval has width less than `P`; this gives a fixed target modulo `2^126`, covered by the repaired truncated NH bound. Identical padded data with different lengths give a nonzero deterministic length term. For the stated block size that term cannot wrap the prime in a way that erases the length distinction.

Thus coefficient-polynomial equality costs at most `2^-62`. Otherwise the root count is at most `N/2^116`. This is sufficient for the subsequent ADU composition; the paper's `N/2^115` allowance is looser.

Split the resulting canonical field value into quotient and remainder to base `q−2^32`. Both coordinates are below `r`, and the splitting is injective. The final map is

`(v1+k1)(v2+k2) mod r`,

with independent uniform field keys. For two different input pairs, its difference expands to a linear expression in the keys with at least one nonzero coefficient. Conditioning on the other key gives every prescribed field difference with probability exactly `1/r`. Therefore

`ε ≤ 2^-62 + N/2^116 + 1/r = V(L)`

is a complete rigorous bound for equality, and also for ADU in the additive group `Z_r`. It implies Theorem 1's advertised formula. This closes the theorem-level gap, despite the false intermediate NH sentence.

A fixed difference modulo `q` has at most two possible integer lifts within `−(r−1),…,r−1`, giving the source's doubled bound for general `Z_q`-ADU. For **equality**, there is only lift zero: doubling is unnecessary.

For a positive affine function of `ceil(L/16)` in the denominator, `L/ε(L)` increases inside each plateau and at successive plateau starts. The minimum is at `L=1`, giving `61.6780719051…` bits. Doubling for general `Z_q` differences subtracts one bit. Two fully independently keyed copies give `V(L)^2`, scoring `123.3561438102…` at `L=1` on the stated `L≤2^56` domain. Over that domain the squared linear growth is far too small to create a lower later minimum; beyond it the domain must be reconsidered.

The VMAC draft's multi-output shared keys and AES-derived material are not the same as two independent ideal VHASH instances. Equality of its full output implies first-component equality under that component's ideal marginal, but a squared bound requires the relevant joint argument. Nonce pads and the MAC-forgery game are separate questions. This review certifies the revised **single-output ideal VHASH theorem**, not a new adaptive security theorem for VMAC.

**Verdict: gap closed with argument for revised VHASH; the stronger unmodified-NH sentence is false.** The shared-key implementation transfer remains undecidable from this single-output argument.

**Proposed author note:**

> The unequal-length claim for unmodified NH in §1.1 has a zero-extension counterexample: one extra product is zero with probability `2^(1−w)−2^(-2w)`. The VHASH theorem appears to survive unchanged. After truncation modulo `2^126`, counting the extra product gives maximum point probability `2^-63`, below the required `2^-62`; the monic polynomial and final field-product stages then complete the proof. I would suggest replacing that intermediate sentence with the truncated argument. For whole-output equality, Theorem 1 already applies without the factor of two from Corollary 2.
>
> For the shared-key multi-output VMAC variant, could you identify the joint theorem and its key-distribution assumptions? Squaring the single-output equality bound is justified for independent copies, but that argument alone does not certify shared keys or the adaptive MAC game.

## 6. Multiply-shift and pair-multiply-shift

Primary sources: [Dietzfelbinger–Hagerup–Katajainen–Penttonen](https://hjemmesider.diku.dk/~jyrki/Paper/CP-11.4.1997.pdf), Lemma 2.4; [Thorup, arXiv:1504.06804](https://arxiv.org/pdf/1504.06804), Theorems 3.5/3.7 and Exercises 3.10/5.1. These are the relevant integer-arithmetic constructions; the tabulation survey has a different arXiv identifier.

### 6.1 Odd one-word multiplier

For `h_a(x)=high_r(ax mod 2^w)`, with uniform odd `a`, write `x−y=2^s z` with `z` odd. Multiplication by `z` permutes the odd residues. The product difference has exactly `s` low zero bits, the next bit one, and uniform higher bits. If `s≥w−r`, two distinct products cannot fall in one output bucket. Otherwise equality requires the nonzero modular difference to lie in the two intervals within one bucket-width of 0. Their combined probability is at most `2^(1−r)`. This is exactly the primary theorem's bound, and the audit has not introduced a gap. At `w=4,r=2`, inputs 1 and 3 collide for four of the eight odd multipliers, so the factor two is real.

For `r=w`, multiplication by an odd integer is a permutation, giving zero collisions, not merely the loose factor-two bound. Its floored 64-bit score is 64; without that convention the one-word permutation has infinite score. For a general `r`-bit output on a single 64-bit word the published loose score is `r−1`.

### 6.2 Vector and paired constructions: completing the exercise

Let input coordinates lie in `[0,2^w)`, and all multipliers plus offset `b` be independent uniform `W`-bit words, with `W≥w+r−1`. For a nonzero vector difference choose its least 2-adic valuation `s`. Then `s≤w−1`. In the dot-product difference, conditioning on all but one multiplier attaining `s` leaves

`g(y)−g(x)=2^s(odd·a_j+constant) mod 2^W`.

Thus its bits from `s` upward are uniform. Independently adding `b` makes `g(x)+b` uniform and independent of that difference. Their high `W−s`-bit values are consequently independent uniform values; the selected `r` bits lie in this region. This proves exact pairwise independence and AU `2^-r`.

For the pair construction, expand

`Σ (a_(2i)+x_(2i+1))(a_(2i+1)+x_(2i))`.

On subtraction, every key-key term cancels. The random linear terms are the same as for the dot product, while the extra constant is `Σ(y_(2i)y_(2i+1)−x_(2i)x_(2i+1))`. Each of its summands is divisible by `2^s`. The preceding argument therefore applies without change. This supplies the exercise's proof. Products/additions are `W`-bit arithmetic; reducing each operand to `w` bits first would instead produce a different construction.

For even prefixes, use an independent unused offset indexed by the length. At unequal lengths, expose everything except the longer prefix's offset. That offset makes the longer output uniform independently of the shorter output, which is itself uniform. At equal lengths use the paired proof above. A partial byte word still needs an injective encoding.

These 64-bit-output families score 64 when a one-word input is admitted; a literal two-64-bit-word pair domain starts at score 65.

### 6.3 What the implementation qualifications establish

For an implementation storing `L+1` **128-bit** keys, the resident count in 64-bit words is `2(L+1)`, so a table reporting `L+1` in those units is wrong for that implementation. A `W=128` version suffices for `w=r=64`; the theorem's minimum width is 127. The supplied workspace lacks the cited benchmark header, so the claimed specific `VectorMultShift` limit and ignored-tail behavior are not independently verified here.

The general failure modes are exact: if a linear/pair-sum implementation cycles key positions, swapping two words/pairs at positions with the same coefficient leaves the sum unchanged for every key. A same-length tag cannot repair that collision. If leftover bytes are ignored, distinct strings differing only there collide deterministically. These are conditional consequences of those code patterns, not findings about files I did not inspect. No small-seed expansion automatically supplies the product key distribution.

**Verdict:** the mathematical bounds hold; the paired and prefix exercises are **closed with argument**. The named benchmark transfer is **undecidable from the supplied code record**, not a gap in Dietzfelbinger et al.'s theorem.

**Proposed author/editor note:**

> I verified the odd-multiplier theorem and completed the strong-universality proof for the paired construction. The mathematical bounds need no correction. Please identify which variant the benchmark row implements, including input cap, partial-word handling, offset, multiplier width, and key distribution. If it uses 128-bit keys, its resident key size in 64-bit words is `2(L+1)`. Cycling key indices would require a separate bounded-domain statement. These are implementation-transfer qualifications, not objections to the published multiply-shift theorem.

## 7. CLHASH and CLNH recheck

Primary source: [Lemire–Kaser, arXiv:1503.03465](https://arxiv.org/pdf/1503.03465), Lemmas 4–5 and 9, Algorithm 4. I checked the actual algorithm and its 126-bit polynomial-key domain.

For CLNH, choose a differing data word. XORing the two product sums cancels every key-key term. Condition on all keys except the one paired with that data difference. The equation is `δk=C` in `F_2[X]`, with `δ≠0`; there is at most one solution among the `q` keys. This proves full-width `q^-1`-AXU, even though the unreduced result has 128 bits. After reduction by the irreducible degree-64 polynomial, multiplication by the nonzero field element is a bijection, so the reduced bound is exactly `q^-1` for every XOR target.

The two binary moduli pass independent Rabin irreducibility checks in the support script. Each unreduced block value has polynomial degree at most 126, so it embeds injectively in `GF(2^127)`. For fixed equal long lengths, equality of all block hashes is contained in the collision event of any one predetermined differing block, costing `q^-1`; reusing the block key across positions needs no union factor. Otherwise the Horner difference is nonzero of degree at most `n−1`, evaluated on `2^126` equally likely points. Lazy reduction preserves congruence to the field value, so equality of lazy representatives implies field equality. The independently keyed final CLNH costs another `q^-1`. Thus the audit's equal-length bound `2/q+(n−1)/2^126` is sound.

For unequal byte lengths `<q`, the independent length key multiplies a nonzero difference in `GF(q)` and makes the output XOR difference uniform. This proves `1/q` even across the short/long algorithm branches. At equal lengths up to 1024 bytes only the initial CLNH is needed. Algorithm 4 therefore has exactly the certificate shown in the table, scoring 64 at `L=1`. For `L>128`, `ε(L)≤L/q`, so no later length lowers the score.

There is a useful minor correction to the audit's endpoint caution. Its restriction to `<q` bytes is sufficient for the sharper unequal-length `1/q` argument. But the paper's **looser global `2.004/q` lemma can also be repaired at the inclusive `q`-byte endpoint**. The only length-encoding alias is length 0 versus length `q`. Condition on everything except the independent long-branch final keys. Their two field factors are independent uniform, so any prescribed product has probability at most `(2q−1)/q²<2/q`. The long equal-length formula is still below `2.004/q` at `n=2^54`. Thus the endpoint is not by itself a counterexample to Lemma 9's global headline.

The source sentence claiming `1/q` regardless of whether lengths agree is overbroad for equal long messages; Algorithm 4 and Lemma 9's actual long-message formula resolve that editorial inconsistency. A common output permutation preserves AU, but not arbitrary AXU. If an implementation mixes only the short branch, the exact cross-branch `1/q` claim needs another argument; the independent long final-product bound still gives a global AU envelope below `2.004/q`. No theorem about PRNG-expanded keys follows from this reasoning.

**Verdict:** the audit's ideal CLHASH/CLNH bounds hold. No new collision-proof gap was found; its endpoint restriction can be relaxed for the coarse global CLHASH bound.

**Optional author/editor note:**

> The Algorithm 4 collision proof checks out with the stated full random key. The sentence asserting `1/q` for all lengths should distinguish unequal lengths from equal long inputs. The global `2.004/q` lemma can still include the endpoint of `q` bytes by treating its length-encoding alias with the independent final-product keys. Please distinguish CLNH's length-proportional key from full CLHASH's fixed-size block key and outer polynomial.

## 8. Simple tabulation recheck

Primary source: [Pătraşcu–Thorup, The Power of Simple Tabulation Hashing](https://arxiv.org/pdf/1011.5200). For fixed character positions, let every table entry be an independent uniform `r`-bit word and XOR the selected entries.

For two distinct inputs, an entry present in one and absent from the other is fresh after conditioning on all other entries. Their output difference is uniform. For three distinct inputs, at some position a character is unique to one input: if no position had a singleton, every position would have all three characters equal, contradicting distinctness. The corresponding entry gives that output an independent uniform value; the other two outputs have the already-proved pair distribution. This yields exact 3-independence and collision probability `2^-r`. Four corners of a two-character rectangle have output XOR zero identically, showing why 4-independence is not claimed.

For a family admitting an 8-byte key and a 64-bit output the score is 64 at `L=1`. For a single universe of fixed size `L0` words it is instead `64+log2 L0`; one cannot change normalization silently.

Variable-length inputs require an injective position/length encoding. If strings are first reduced by an independent family of error `e`, composition with tabulation gives `e+(1−e)2^-r`, not `2^-r`. A PRNG-generated table is not automatically the theorem's independent table. The audit's mathematical verdict holds; composite implementation allegations cannot be verified from the absent benchmark source alone.

**Proposed editor note for a composite row:**

> The pure simple-tabulation theorem applies to independent position-specific tables on a fixed character universe. If the benchmark first compresses arbitrary strings, please give that compressor's bound and add the conditional tabulation term. The name “tabulation” alone does not transfer the pure family's guarantee to the complete wrapper.

## 9. Polynomial hashing, Mersenne fields, and BRW recheck

Primary sources: [Carter–Wegman 1979](https://bpb-us-w2.wpmucdn.com/u.osu.edu/dist/7/36891/files/2020/10/CarterWegmanJrCompSci1979UniversalHashClasses.pdf), Lemma 6 and Proposition 7 on printed p.149 (scan visually checked and OCR'd); [Bernstein, Polynomial evaluation and message authentication](https://cr.yp.to/antiforgery/pema-20071022.pdf), §§4.2 and 5.2–5.7. These are distinct constructions, not one interchangeable theorem.

### 9.1 Affine hashing and root-counting families

For the Carter–Wegman affine family, take a prime `p0`, uniform nonzero multiplier `a`, and independent uniform offset `b`. Distinct input field elements map uniformly to ordered **distinct** output field elements: every such ordered pair gives exactly one solution for `(a,b)`. If a balanced map to `B` buckets has fibre sizes `n_j`, collision probability is exactly

`Σ_j n_j(n_j−1)/(p0(p0−1)) ≤ 1/B`,

because `n_j−1≤ceil(p0/B)−1≤(p0−1)/B`. Before bucket reduction the affine maps are permutations. Allowing the multiplier to be zero instead gives exactly pairwise independent full field outputs, with collision `1/p0`. The audit's distinction is correct.

For fixed-length Horner on `d` field symbols, the two formal polynomials differ in a coefficient. Their difference has degree at most `d−1`, hence AU `clip((d−1)/p0)`. This unshifted version is **not** generally ADU: changing only the constant coefficient gives a deterministic difference. Multiplying the data polynomial by the evaluation variable ensures a nonzero positive-degree term, even after subtracting a fixed target, and gives `clip(d/p0)`-ADU. An independent uniform field pad divides each joint-output probability by a further `p0`.

A restricted uniform key set of size `S` replaces `p0` in the root denominator by `S`; arbitrary keys replace it by their maximum point mass. Variable lengths require a separately injective polynomial encoding. Unmarked `(a)` and `(0,a)` give the same unshifted polynomial. A leading marker plus injective chunk/length encoding repairs this.

Mersenne reduction is exact field arithmetic only for a prime modulus and adequate intermediate width: `u·2^b+v≡u+v mod (2^b−1)` does not authorize dropping unrelated overflow bits. Reducing arbitrary 64-bit characters modulo `2^61−1` is not injective: characters 0 and `p` become identical under every key. Use a smaller alphabet or an injective multi-symbol encoding.

### 9.2 Truncation: a real counterexample and a valid repair

The audit's truncation example is correct. Put `B=2^64`, `p0=2^89−1`, and let the two message polynomials be `X` and `X+B−1`, with uniform `X∈F_p0`. Their full canonical field outputs never collide. Their low 64 bits coincide exactly for the `B−1` evaluations at which the second residue wraps modulo `p0`, because `p0≡−1 mod B`. The collision probability is **`(B−1)/p0≈2^-25`**. These polynomials are valid fixed-length two-coefficient inputs with 64-bit coefficients. Replacing `B` by `2^32` and `p0` by `2^61−1` gives the analogous approximately `2^-29` event. This is a counterexample to arbitrary truncation of the full-residue AU theorem.

If an independent finalizer is a uniformly random field polynomial of degree at least 1, evaluations at two distinct inputs are independent uniform field elements: two evaluation rows have rank 2. Truncating **those** values is legitimate. For `p0=B R−1`, their low-log2(B)-bit collision probability is exactly

`ξ=((B−1)R²+(R−1)²)/p0² = 1/B+(B−1)/(B p0²)`.

For an independent first-stage error `e`, the result is `e+(1−e)ξ`. This is an actual conditional joint-distribution argument. It does not apply to an absent finalizer or to correlated PRNG-derived coefficients.

The specific `poly-mersenne.deg0…deg4` code is not supplied here. The audit's mathematical corrections for its stated 32-bit chunking, restricted key set, and 32-bit output follow **if that description is accurate**: a length-prefixed signature on `2L` 32-bit chunks and a uniform set of size `2^60−1` has root bound `2L/(2^60−1)` before truncation. A genuinely independent degree-at-least-one field finalizer gives the composition above with `B=2^32,R=2^29`. I do not certify the actual seed expansion or assert the saved code facts as independently inspected findings.

### 9.3 Scores and the floor convention

For binary-field Horner, `ε(L)=clip((L−1)/q)`. The paper's floor gives score **64 at `L=1`**; for every later length the ratio is larger. If the user intends **no output floor**, the exact finite-cap minimum for `2≤L≤M<q+1` is at `L=M` and equals `log2(Mq/(M−1))`. On an unlimited integer-length domain with probability clipping, the minimum is at **`L=q+1`**, giving `log2(q+1)`, rather than an unattained 64-bit limit. The latter limit pertains only to the formally *unclipped* degree expression. This is a useful precision improvement to the audit's discussion.

For `p0=2^b−1` and one injective field coefficient per 8-byte slot, full `b`-bit unshifted output scores **b** with the floor. If `b>64`, this slot model uses a restricted 64-bit coefficient alphabet, not all `p0` field values per slot. Positive-power `L/p0` scores `log2 p0`. With two 32-bit coefficients per 8-byte word, unshifted degree `2L−1` over `2^61−1` scores **60** on the full byte domain: saturation occurs at `L=2^60` and supplies the minimum. The restricted-key length-prefixed `2L/(2^60−1)` signature scores `log2(2^60−1)−1`, about 59, before output truncation. With the ideal independent 32-bit finalizer above, the score is approximately 32, not 61.

### 9.4 BRW's exact bases and degree

Bernstein defines `H()=0`, `H(a)=a`, `H(a,b)=aX+b`, and `H(a,b,c)=(X+a)(X²+b)+c`. For `n≥4` and `t=2^floor(log2 n)`,

`H(m)=H(m1,…,m_(t−1))(X^t+m_t)+H(m_(t+1),…,m_n)`.

The left polynomial is monic of degree `t−1`; the right has degree at most `t−1`. Thus the leading degree is `2t−1`, without cancellation. Reading degrees `t,…,2t−1` recovers the left polynomial and recursively its message. After subtracting its `X^t` multiple, degree `t−1` gives `m_t` plus the known leading coefficient of the right polynomial (0 or 1 for the known right length). Recover `m_t`, subtract its multiple of the left polynomial, and recurse on the right. This proves fixed-length injectivity.

The leading monomial cancels between equal-length messages, so the raw difference degree is

`d_B(1)=0`, `d_B(2)=1`, `d_B(n)=2^(floor(log2 n)+1)−2` for `n≥3`.

This gives raw AU `clip(d_B(n)/q)`. Bernstein's authenticator `XH_X(m)+s` adds a degree and an independent pad; its convenient `(2n−1)/q` envelope is not the sharp raw degree. His variable-length theorem requires its stated alphabet separation conditions, or an independently proved length encoding.

The local paper's simplified `P()=1` recursion has different small bases. In particular its two-symbol difference can have degree 2, rather than Bernstein's degree 1. Its fixed-length injectivity still follows by the same degree-separated decoder. The local sentence that sums of monic polynomials are monic is false in general; **degree separation** supplies the needed fact here. Neither this sentence nor the altered base cases invalidate the stated loose `(2n−1)/q` AU envelope.

For `M=2^61−1`, the loose envelope's score is minimized at `L=M`, with exact value `64+log2(M/(2M−1))`. The sharper raw staircase is minimized at `L=2^60`, with value `63−log2(1−2^-60)`. Both round to 63. If all positive integer lengths are allowed, the respective minimizers are `2^63` and `2^63`, with scores `63+log2(q/(q−1))` and `63−log2(1−2^-63)`. The audit's numerical/domain distinctions are correct.

**Verdicts:** the field-root, affine, and BRW arguments are **closed with the explicit domain/output/base-case corrections**. Horner over `GF(q)` holds as audited. Blind truncation has an actual counterexample; seeded implementation transfer remains undecidable from the supplied files.

**Proposed author/editor note:**

> The full-field root-count bounds check out. Please state the coefficient packing, evaluation-key distribution, length encoding, and retained output bits for each row. Full-residue AU does not survive arbitrary truncation: `X` and `X+2^64−1` modulo `2^89−1` give a low-64-bit collision probability near `2^-25`. An independent random-polynomial finalizer can justify truncation with its own composition bound. For BRW, please distinguish Bernstein's raw bases from the manuscript's `P()=1` variant and attribute monicity to degree separation; the loose advertised AU envelope remains valid.

## 10. The supplied recurrence and ChainHash proofs

Primary sources here are [paper/injective.tex](paper/injective.tex) and [paper/appendix_chainhash.tex](paper/appendix_chainhash.tex). The audit has no full recurrence/ChainHash section after its BRW section, so I reconstructed these arguments directly from the TeX rather than relying on its summary table.

### 10.1 Recurrence injectivity, including the small cases

For `P_0=z`, `P_i=a_i+(b_i+y)(P_(i−1)+u)`, put `g_i=product_(j=i)^n(y+b_j)` and `g_(n+1)=1`. Expansion gives

`P_n=A(y)+z B(y)+u C(y)`,

`A=Σ_i a_i g_(i+1)`, `B=g_1`, `C=Σ_i g_i`.

To decode an ordered list of `m` remaining `b` values from the corresponding `(G,S)`, use

`b_first = [y^(m−1)]G − [y^(m−2)](S−G) + 1_(m≥3)`.

For `m=1`, read the negative-degree coefficient as 0. For `m=2`, the indicator really is absent. Update simultaneously `(G,S) ← (G/(y+b_first), S−G)`, using the old `G` on the right, and repeat. This recovers the **order** of the `b_i`, not just their multiset. The degrees of the monic `g_(i+1)` then successively reveal the `a_i` from `A`. The coefficient map is injective over every field, including characteristic 2.

Both `B` and `C` are monic of degree `n`, whereas `deg A≤n−1`. The common total-degree-`n+1` part is `(z+u)y^n`; it cancels between two distinct same-length messages. Schwartz–Zippel with three independent uniform field keys gives `n/q`. Fixed padding of an odd word count gives the table's `ceil(L/2)/q`; it does not by itself license unmarked variable lengths.

The one-key substitution `y=X³,z=X,u=X²` preserves injectivity because the three summands occupy distinct exponent classes modulo 3. Its three top coefficients are message-independent, giving `(3n−1)/q`. The two-key substitution `z=X,u=X²`, with independent `y`, is also injective as a formal polynomial in `(X,y)` and has difference degree at most `n+1`, giving `(n+1)/q`. These are distinct families.

One minor wording correction: `P_n` is **not monic in `y`** over `F[u,z]`; its leading coefficient is `z+u`. It is `B` and `C` that are monic. The supplied proof uses precisely those polynomials, so this wording issue does not invalidate the degree/collision argument.

For eight fixed interleaved lanes, use the same recurrence keys and an independent uniform combining key `v`, outputting `Σ_(j=0)^7 P_j v^j`. At a fixed length the lane lengths are fixed, and a differing lane supplies a nonzero coefficient of this formal polynomial in `v`. Its total difference degree is at most `ceil(ceil(L/2)/8)+7`. The stated bound and 61-bit score follow. The one-chain score is 64 if length-one padding is admitted, otherwise 65 on the even-only input domain.

### 10.2 The 89-bit row: do not turn missing code into a factual accusation

The abstract argument works over `F_(2^89−1)`, with full residue output and field-uniform keys. The three-key fixed padded-word bound is `ceil(L/2)/(2^89−1)`; its score is `log2(2^89−1)≈89` at `L=1`, or `log2(2(2^89−1))≈90` on the unpadded even-only domain. The output floor does not change these minima for that displayed envelope. The two-key specialization instead gives `(ceil(L/2)+1)/(2^89−1)`, scoring `log2((2^89−1)/2)≈88` for that loose envelope when `L=1` is admitted. Different 15-byte packing requires its own degree and length normalization.

The current supplied table explicitly labels the output as **89 bits** and warns about low-64-bit truncation. The audit and `provable.json` allege that a particular timed harness used a restricted two-key/truncated version. That harness is not present. Therefore I cannot independently confirm which code generated the timing, nor certify the 88-bit timed row. It would be wrong to present this second reading as having inspected that implementation. The right verdict is **undecidable from the supplied files**, with a concrete request for the timed definition/key sampler. The valid abstract recurrence theorem is not in doubt.

**Proposed manuscript-author note:**

> The recurrence's coefficient decoder and degree bounds check out, including the `n=2` indicator. The supplied table now states a full 89-bit output. To certify the 88-bit timed row, please identify the exact timed source, packing, and key sampler: the three-key and two-key recurrences have different bounds, and the audit refers to a harness not included here. I cannot independently confirm its alleged truncation. Also, please replace “P_n is monic in y” with the precise statement that its z and u coefficient polynomials are monic.

### 10.3 ChainHash's length handling is sound

The block compressor keeps both halves of unreduced CLNH. The equal-pair-count full-width AXU proof is the integral-domain argument in §7. For unequal pair counts and a **nonzero** XOR target `C`, start with the common-prefix difference, whose target probability is at most `1/q` or is zero if the prefixes agree. Adding one independent carryless product gives

`p_new ≤ (1−1/q)/q + p_old/q ≤ 1/q`.

This is valid because a nonzero first polynomial factor makes the equation injective in the second; the zero-factor case leaves the old event. It would be false at a zero target with identical prefixes, which is why the length term matters.

At equal block count but unequal byte lengths, equality of the final stream pair requires the nonzero target

`C=(length xor length')·(1+X^64)`

in `F_2[X]`. The two 64-bit lengths are distinct for byte lengths `<q`. Same padded final contents therefore separate deterministically; different contents at the same pair count use AXU; unequal pair counts use the preceding nonzero-target lemma. At equal byte length, pick any predetermined differing sub-block. Whole-stream equality is contained in that one collision event, so reusing block keys adds no factor. Different block counts give different stream lengths and can never have equal streams.

Thus stream equality costs at most `1/q` when block counts agree and costs zero when they differ. For different stream lengths, the recurrence difference has degree `max(p,p')+1`, because its top `(z+u)y^max(p,p')` term no longer cancels. This extra degree is correctly paid for in the appendix: it occurs precisely where the stream-collision term disappears.

### 10.4 The finalizer is a uniform monic polynomial, and the twist is free for this theorem

Write `b=c0+c1`, `d=c0c1`. Expanding the three-multiplication circuit gives

```
e5 = 1
e4 = 1+c2
e3 = b+c2
e2 = c0+c2 b
e1 = d+c3+c0 c2
e0 = c4+c2(d+c3).
```

In characteristic 2, recover `c2=e4+1`, then `b=e3+c2`, `c0=e2+c2b`, `c1=b+c0`, `c3=e1+c0c1+c0c2`, and `c4=e0+c2(c0c1+c3)`. All pivots are units; no root or division is needed. This is a bijection from the five circuit parameters to the five free coefficients. Independent uniform parameters therefore produce a uniform monic degree-5 polynomial.

At distinct field inputs, conditioning on every coefficient except the linear one gives exactly `1/q` collision probability. Up to five distinct inputs give a full-rank Vandermonde system and exactly uniform joint outputs. The integer addition `v↦v+τ mod q` is a bijection for every `τ`; condition on `τ` and the earlier stages, and these statements still apply. This is a legitimate use of a permutation because the **finalizer's conditional joint distribution** is known, unlike the Polymur ASU proof step.

If `p=Sn` is the maximal recurrence step count, equal block counts cost at most `(1+p+1)/q`; unequal counts cost at most `(0+(p+1)+1)/q`. Both give `(Sn+2)/q`. The three block-size bounds and scores in the table follow, with minimum at `L=1`.

The appendix's qualified five-wise statement also survives: earlier-stage equality of any pair costs at most `(p+1)/q`. A union bound over at most `binom(t,2)` pairs bounds the probability that the `t≤5` finalizer inputs fail to be distinct. On the complement their conditional joint distribution is exactly uniform, giving the stated total-variation error. It is **not unqualified exact five-wise independence of arbitrary original strings**.

**Verdict:** the recurrence and ChainHash collision bounds **hold as stated under their ideal-key and arithmetic assumptions**. No new proof gap was found. The seeded ChainHash caveat is already explicit in the current appendix; the theorem does not certify that subfamily, but neither does the caveat show that its bound is false.

**Proposed editor note for the implementation distinction:**

> The supplied ChainHash collision theorem checks out, including unequal block counts, the nonzero length target for unequal CLNH pair counts, and the characteristic-2 finalizer decoder. Keep the existing distinction between the ideal `W+9` independent field words and the timed 64-bit-seed subfamily. The latter needs its own distribution argument; this is not a flaw in the ideal theorem. The five-wise result should retain its stated variation-distance qualification.

## 11. What should change before making a public claim

1. **Do not report a broken VHASH collision theorem.** Its overly strong intermediate NH sentence is false, but the actual theorem has a complete repair with room to spare.
2. **Do not report that no standardized UHASH collision bound can be certified.** The exact 32-bit RFC hash-equality envelope is certified above. The checked-source uncertainty concerns the stronger shared-key multi-component bound and the full MAC transfer.
3. **Do not portray the audit's 39.3923-bit HalftimeHash repair as the best rigorous consequence.** Partial-coordinate EHC bounds recover a 96-bit score for a corrected abstract 24-byte core. The original Lemma 3 still needs replacement, and the fetched `Encode3` failure is real.
4. **Polymur's numerical key-count issue is repairable.** Use the explicit lower bound above for the ideal model. The deleted degree constant, ASU counting, and seed distribution remain separate unresolved points.
5. **UMASH needs a projection lemma, not another entropy-loss estimate.** The omission is confirmed; the claimed production inequalities have not been disproved here. Keep conditional headline-score calculations clearly separate from certificates.
6. **Do not turn unavailable code into newly verified findings.** In particular the 89-bit row and benchmark multiply-shift/prime-polynomial wrappers need the actual timed implementations. In `paper/related.tex`, the length-proportional-key statement should name CLNH, not full CLHASH.
7. **State the score's output floor and length domain.** A constant-size collision probability, a conditional pointwise bound at 1 MiB, and the minimum of `log2(L/ε(L))` are different quantities.

The author notes above are drafts only. They deliberately identify the precise missing implication and the result that survives, without equating an incomplete proof with a demonstrated failure of the advertised hash.

## Reproduction and source record

* Run `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 review-support/checks.py` for the integer/rational calculations, minor certificates, intended encoder ranks, binary irreducibility and Mersenne primality checks, the GF(4) finalizer decoder, tiny multiply-shift distributions, and finite proof-step witnesses. Python 3 and SymPy are used; no stochastic evidence is needed for the certified constants.
* Run `clang++ -std=c++17 -O2 -U__ARM_NEON -U__ARM_NEON__ review-support/halftime-check.cpp -o review-support/halftime-check` and then the executable for the fetched scalar `Encode3` witness. This is a focused encoder test, not a full implementation equivalence test.
* The [manifest](review-support/sources/MANIFEST.tsv) records the exact fetched bytes and primary URLs. Repository links track branches; the saved SHA-256 values identify the material actually reviewed. The [2006 VMAC paper](https://krovetz.net/csus/papers/vmac.pdf) was also fetched and checked: it uses the older 61-bit final field, a different polynomial/length arrangement, and a different 128-bit construction. Its constants cannot certify the revised 2007 algorithm by substitution.
* The original audit's `gathered/` and `audit-support/` links are absent in this workspace. Their claimed code tests were not silently treated as available evidence. The new support directory contains this review's own downloads and computations.
