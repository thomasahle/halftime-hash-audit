# Adversarial referee report: the HalftimeHash 64-bit wrapper certificate

**Verdict: HOLDS.**  I attempted to refute the claim and could not.  Every load-bearing
step reproduces under independent recomputation from `halftime-current.hpp`
(SHA-256 `7ef5dd48f54537b430f85bc1867b23a93551ab1c56415cfcef362d1651956cc3`, identical to
`review-support/sources/halftime-hash.hpp`).  Two cosmetic corrections are listed in §C;
neither touches a probability, an index, or the score.  No counterexample pair exists to
be constructed: the one step that could plausibly have been circular (§6's overlap
handling) is *structurally* immune, for the reason given in §B.

Scripts: `recheck.py`, `recheck2.py` in this directory.  I recomputed every index and
minor from the header's source text, not from PROOF.md's tables.

---

## A. Steps checked, with independent recomputation

### A1. Key layout and absolute indices (recomputed from the code)

`TabulateAfter<Hasher, width=2>` binds `table` to the caller's array at offset 0 and then
does `entropy += width*256` — **512** words, while the three `TabulateBytes<8>` calls it
issues consume rows 0–7, 8–15 and 16–23, i.e. words 0–6143.  The overlap is therefore
real and is exactly as PROOF §2.1 describes.

| Region | My computation | PROOF §2.1 | agree |
|---|---|---|---|
| length-byte tables | 0 … 2047 | 0 … 2047 | ✓ |
| core entropy base | 512 | 512 | ✓ |
| EHC symbol keys (`entropy_matrix[i][j]=entropy[3i+j]`, i<7, j<3) | 512 … 532 | `512+3s+t` | ✓ |
| tree keys (`&entropy[21+14j]`, index `7c+(v-1)`), 9 levels reserved | 533 … 658 | `533+14j+7c+(v-1)` | ✓ |
| finalizer base (`entropy += 21 + 2·7·9 = 147`) | 659 | 659 | ✓ |
| stack node v, coord c, lane ℓ (`Insert(const Block(&)[2])`, `seeds += b` per coord) | `659+b(2v+c)+ℓ` | same | ✓ |
| raw block t, coord c, lane ℓ (`Insert(Block)`, `LoadBlock(&seeds[c·b])`, `seeds += b`) | `p+b(t+c)+ℓ`, `p=659+2bs` | same | ✓ |
| out-0 / out-1 byte tables (`&table[8][0]`, `&table[16][0]`) | 2048…4095 / 4096…6143 | same | ✓ |

Largest core read index, taking `s ≤ 64` live nodes and `T ≤ 18` raw blocks
(`(144b−1)/(8b)+1 = 18`, verified):

| b | last stack key | p | **last core key** | PROOF |
|---|---|---|---|---|
| 1 | 786 | 787 | **805** | 805 ✓ |
| 2 | 914 | 915 | **952** | 952 ✓ |
| 4 | 1170 | 1171 | **1246** | 1246 ✓ |
| 8 | 1682 | 1683 | **1834** | 1834 ✓ |

`1834 < 2048`.  The separately-run `layout-check` binary traces actual `LoadBlock`
addresses in the maximal state and reports `finalizer_last = 658+147b`,
`distinct_words = 147b` — matching my arithmetic exactly.  **The claim that the overlap
reaches only the length tables, and that all sixteen output-byte tables are untouched by
the core, is correct.**

`kEntropyBytesNeeded` recomputed from the header's own `FloorLog` chain:
`256·3·8·8 + 8·(21+14·18+128·18+144+1) = 70 928` bytes `= 8 866` words.  Matches.

### A2. The finite stack and the certified length domain

Simulating `DfsTreeHash`'s `stack_lengths` for n < 3000 confirms it equals the **bijective
base-8** digits of n (digits in 1..8, no zero holes) — PROOF §2.2's induction is right.
`C8 = 8+…+8^8 = 19 173 960`; `digits(C8) = [8]×8` (sentinel `stack_lengths[8]=0` survives),
`digits(C8+1) = [1]×9` (the finalizer's `for (j=0; stack_lengths[j]>0; ++j)` then reads
index 9).  So `n ≤ C8`, `length < 144b(C8+1)`, is exactly the largest safe contiguous
domain, and the byte limits 2 761 050 384 / 5 522 100 768 / 11 044 201 536 / 22 088 403 072
and the word caps 345 131 297 / 690 262 595 / 1 380 525 191 / 2 761 050 383 all reproduce.
Max live nodes `s = 64` (8 digits × 8) — the bound `s ≤ 64` is tight and attained.
Max `EhcUpperLayer` level actually used is **j = 6** (from `digits(C7)=[8]×7 ⇒ i=7`),
inside the 9 reserved levels; PROOF's statement matches.

I also verified the structural fact the tree bound needs: the top live level `d` satisfies
`d ≤ floor(log_8 n)` for all n (checked exhaustively to 200 000 and at every `C_k`, `C_k+1`
boundary), so the chain length from a differing leaf to its live ancestor is `≤ h`.

### A3. NH / Encode2 distance / the minors

* **NH one-pair ADU (§3).**  `Mix` computes `accum + ((x_lo+s) mod 2^32)·((x_hi+t) mod 2^32)`
  (`Plus32` then `Times` = `low32·low32` of value and its `>>32`).  I re-derived the
  straddling-wrap case: with `e=c−c'≠0`, `m=k₂−k₁∈[1,Q−1]`, the quantity `em+c'Q` lies in
  `(0,Q²)` in both sign cases (`c>c'`: `≤(Q−1−c')(Q−1)+c'Q = (Q−1)²+c' ≤ Q²−Q−1`;
  `c<c'`: `≥ c'(Q−m) ≥ 1`).  The argument is correct; `a = 2^-32`.
* **Toeplitz raw suffix.**  Flattening `(t,ℓ) ↦ q = bt+ℓ` gives
  `output[c] = Σ_q N_{K[p+q+cb]}(w_q)`, a Toeplitz NH with shifts `0` and `b` *words*
  (one Block), as claimed.  Taking the last differing flat index `Q*`, `K[p+b+Q*]` is
  absent from `Δ₀` (whose keys are `p..p+Q*`), so conditioning gives `a` for each
  coordinate and `a²` jointly.  Correct.
* **Encode2 distance = 2.**  `io[6][i] = ⊕_{j<6} io[j][i]` is a systematic single-parity
  code on 6 symbols; one changed input symbol ⇒ exactly 2 changed encoded symbols, two or
  more ⇒ ≥2.  Exactly 2, per-lane as well (XOR acts lanewise).  ✓
* **Combine2 matrix, read off the code** (`output[0]=input[0]`, `output[1]=input[1]`,
  `Dot2<1,1>,<1,2>,<2,1>,<1,4>,<4,1>` on inputs 2..6):
  `T = [[1,0,1,1,2,1,4],[0,1,1,2,1,4,1]]`.  ✓
* **Minor certificates, recomputed independently for all 21 pairs** (`recheck.py`).  I did
  not take `2^{v2(det)}` on faith: I computed `|ker A|` over `Z/2^64` via integer Smith
  normal form (`d₁ = gcd of entries`, `d₂ = |det|/d₁`, `|ker| = gcd(d₁,2^64)·gcd(d₂,2^64)`)
  and confirmed it equals `2^{v2(det)}` in all 21 cases.  Every determinant is nonzero
  (values 1, ±1, ±2, ±3, ±4, ±7, −15).  Results:
  **max(c₀+c₁) = 5** and **max c_{0,1} = 4**, both attained at `F={0,5}` and `F={1,6}`
  — exactly as claimed.  Singleton kernels exceed 1 only for `F ⊆ {1,4,6}` (row 0) and
  `F ⊆ {0,3,5}` (row 1), which is why 5 is the maximum of the sum.
  For `|F| > 2` the constants only improve, since `c_S` is a minimum over column subsets.

### A4. The core theorem (§5)

I re-derived each ingredient rather than checking the prose.

* Conditional on the 21 EHC key words, `I_0` and `I_1` are constants and the two
  coordinates' remaining key sets are **disjoint**: tree keys `7c+(v−1)` split 0–6 / 7–13
  at each level; finalizer stack keys split `659+2bv+[0,b)` / `659+2bv+b+[0,b)`.  The
  Toeplitz raw keys *do* overlap across coordinates, but with equal tails those terms
  cancel identically in both differences, so they cannot couple `A_0` and `A_1`.
  Conditional independence therefore holds — this is the step I most expected to fail and
  it does not.
* `Pr[A_c | EHC] ≤ ρ + (1−ρ)I_c` with `ρ = (h+1)a`: the chain bound `h·a` follows by
  conditioning level by level (only one differing chain is tracked, so key reuse inside a
  level is irrelevant); the pass-through child 0 of `EhcUpperLayer` makes collision
  *impossible* when only it differs; the final NH costs `a` using one fresh
  `K[659+b(2v+c)+ℓ]`, which is per-lane (`LoadBlock`, not `LoadOne`) and used exactly once.
* `E[(ρ+(1−ρ)I₀)(ρ+(1−ρ)I₁)] ≤ ρ² + 5aρ + 4a²` uses `(1−ρ)≤1`, `E[I_c] ≤ c_c(F)a`,
  `E[I₀I₁] ≤ c_{0,1}(F)a²`, and `ρ<1` (`ρ ≤ 9·2^-32`).  The algebra
  `(h+1)²+5(h+1)+4 = (h+2)(h+5)` is verified.
* Case coverage is complete: no leaf (Toeplitz `a²`), leaves with differing tails
  (condition on all non-tail keys, Toeplitz `a²`), leaves with equal tails and a differing
  leaf (the above).  "Equal tails and no differing leaf" at equal length means identical
  messages.  ✓

### A5. Score

`min_L log2(L/eps_b(L))` recomputed for b = 1,2,4,8 over all plateau left endpoints
(the only candidate minima) up to each `Lmax`:

| b | L=1 | first leaf L=18b | next | … | min |
|---|---|---|---|---|---|
| 1 | 63.0000 | 64.7105 | 66.9220 | ↑ | **63** at L=1 |
| 2 | 63.0000 | 65.7105 | 67.9220 | ↑ | **63** |
| 4 | 63.0000 | 66.7105 | 68.9220 | ↑ | **63** |
| 8 | 63.0000 | 67.7105 | 69.9220 | ↑ | **63** |

Plateau lengths grow ×8 while `(h+2)(h+5)+1` grows by at most 19/11 ≈ 1.73, so the score
is increasing after the first leaf; within a plateau `eps` is constant so the minimum is
at the left endpoint.  **Score = 63, attained at L = 1.**  The sharp envelope
`u+(1−u)B` gives `64−log2(2−2^-64) = 63 + 3.9104·10^-20` bits, and the `00`/`01` pair
recomputes to exactly `2^-63 − 2^-128`: the core difference in lane 0 is `−t` (or
`(Q−1)t` when the low key half is `Q−1`), zero iff the high key half `t = 0`, for the two
independent words `K[659]` and `K[659+b]`, giving core collision exactly `2^-64`, then
`u + (1−u)u`.  Both the value and the "attained" claim are right.

---

## B. The delicate step: the overlapping length-table words

The worry is well founded as a *fact*: for essentially every in-domain length, the length
tabulation reads rows 2–7, i.e. words in `[512, 2047]`, which is precisely the core's key
window.  I constructed the sharpest version of the feared configuration:

> **b = 1 (Style64).**  `l = 65 536`, `l' = 131 072`.  These differ only in byte 2, so
> `D = K[513] ⊕ K[514]`.  Words 513 and 514 are `entropy_matrix[0][1]` and
> `entropy_matrix[0][2]` — **EHC symbol-0 key words that both messages' cores read**
> (n = 455 and 910 complete leaves).  Same for b = 8 (n = 56 and 113).
> Choosing lengths that differ in byte 3, 4, 5 or 6 instead puts `D`'s words on tree or
> finalizer keys equally well.

This does **not** refute anything, because PROOF §6 never asserts independence between the
core and the length tables.  Its identity is exact, not an approximation:

```
Pr[H(m)=H(m') | K[0..2047]] = 1[C]·1[D=0] + 1[¬C]·2^-64
```

conditioning on *all* words below 2048 — which fixes both core outputs **and** `D`,
overlap included — and using only that words 2048…6143 are untouched by everything below.
(If `C` is false, the selected differing signature byte's table word appears exactly once
among the 32 output-table lookups, since the 24 byte-rows are pairwise disjoint 256-word
blocks; hence exactly `2^-64`, whatever `D` is.)  Taking expectations gives
`Pr = u·Pr[¬C] + Pr[C ∧ D=0]`, and the only remaining step is
`Pr[C ∧ D=0] ≤ Pr[D=0] = 2^-64` — a *marginal* statement about `K[0..2047]` that is true
however strongly `C` and `D` are correlated.  Even in the adversary's dream case
(`D=0 ⇒ C` and `Pr[C]≈0`) the bound is `2u = 2^-63`, which is exactly `eps_b(L)` in the
short-input regime, so the envelope is not merely safe but tight against that attack.
**There is no exploitable configuration to find; conditioning destroys no freshness
because the freshness used lives entirely above index 2047.**

Cross-check: `header-check.cpp`'s `wrappers()` verifies on real executions, for all four
styles and 13 lengths each, that the shipped wrapper equals
`⊕_{word<3,byte<8} key[(8·word+byte)·256 + byte_of(sig[word])]` with
`sig = (len, core[0], core[1])` and the core called at `key + 512` — i.e. it verifies the
flat-address formula the proof reasons about, not a re-implementation.

---

## C. Corrections (both cosmetic; nothing propagates)

1. **§8.1, "depend only on the first four raw blocks" — should be six.**  I evaluated
   `Encode3`'s frozen-capture behaviour symbolically: `DistributeRaw` copies
   `iter = io[1]` at lambda-creation, so every distribution reads blocks 3,4,5; the
   initialisation reads `io[0]` = blocks 0,1,2.  The net effect is
   `io[7] = io[0]` (the 8-iteration `while` loop XORs `io[1]` an even number of times and
   cancels) and `io[8] = io[0] ⊕ io[1]` (the 6-call parity matrix is the identity, which I
   computed).  So the parity symbols depend on the first **six** raw blocks / first two
   encoded symbols.  The witness (block `6b` = symbol 2) is outside both, so the
   distance-1 conclusion and the `2^-32` fibre count are unaffected — if anything the
   real structure is worse than described.
2. **§5, "Subsequent height-boundary lengths grow by eight while the coefficient grows by
   at most 18/10 < 8"** describes `B_b`; §7 repeats it for `eps_b`, whose ratio is 19/11.
   Both are < 8 so the conclusion is unchanged; the sentence in §7 quotes §5's constant.

## D. Qualifications that are correctly disclosed (not defects in the proof)

* The `table[8]` / `table[16]` accesses are out of the declared `[1+width][256]` bound
  (UBSan log confirms at header line 1025); stock NEON dispatch names `V2Neon/V3Neon/V4Neon`
  are never defined; NEON/SSE `Sum` adds signed lanes.  PROOF §1 and §9 scope the theorem
  to the flat-address, modular-arithmetic contract and do not claim portable ISO C++.  I
  agree this is the right scoping and that it is stated, not buried.
* The certificate needs 8 866 *independent uniform* key words; no seeded-PRNG claim is made
  (§1).  Worth restating loudly since the header's own usage example seeds with a
  default-constructed `mt19937_64`.
* Beyond `144b(C8+1)` bytes the finalizer reads `stack_lengths[9]` (ASan log confirms);
  no bound is asserted there, and the score is unaffected because the score's minimum sits
  at `L = 1`.

## E. Plain summary

I tried to break this proof and failed. Recomputing the key layout directly from the
header confirms its numbers exactly: the tabulation advances the core pointer by only 512
words while its own tables span 6144, so the core's key words (512 through at most 1834 on
the safe length domain) really do sit inside the eight length-byte tables, but they stop
well short of 2048, where the sixteen output-byte tables begin, so those tables are
untouched by anything the core or the length lookup reads. The delicate step survives for
a structural reason rather than by luck: §6 conditions on every word below 2048, which
pins the core outputs and the length difference together, overlap and all, and then uses
only the marginal fact that two distinct 8-byte lengths tabulate to the same word with
probability exactly 2^-64 — so however strongly the overlap correlates the two, the bound
is at worst 2·2^-64. I built the sharpest version of the feared witness (lengths 65 536 and
131 072, whose length-table difference falls on EHC key words 513 and 514 that both cores
read) and it is handled without strain. Independently recomputed: Encode2's distance is
exactly 2; all 21 two-column minors of the 2×7 combine matrix are nonsingular, with
maximum singleton-kernel sum 5 and maximum kernel 4, both attained at {0,5} and {1,6},
and I verified the kernel sizes by Smith normal form over Z/2^64 rather than assuming the
valuation formula; the lazy stack really does hold the bijective base-8 digits, capping
live nodes at 64 and the safe leaf count at 19 173 960; and the score
min_L log2(L/eps) is 63, attained at L = 1, with the one-byte pair 00/01 hitting
2^-63 − 2^-128 exactly. Two wording slips exist — the Encode3 parity symbols depend on the
first six raw blocks, not four (I computed that Encode3 in fact produces symbol 7 = symbol
0 and symbol 8 = symbol 0 XOR symbol 1, which is worse than described and strengthens
rather than weakens that section) — but no probability, index, or score changes. Verdict:
HOLDS.
