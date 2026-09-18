# Lean HalftimeHash status

Worktree: `thomas-ahle@hardware.normalcomputing.net:~/agents/lean-halftime`.
Source mirror: [lean/](lean/). All compilation and proof checking ran on the Xeon;
the Mac performed only editing, file reads, and SSH/rsync transport.

| Milestone | Status | Checked result / remaining work |
|---|---|---|
| M1 | **COMPILED** | Integer NH, correctly scoped unhashed accumulator, and sharp mod-2^62 AΔU for every target. |
| M2 | **COMPILED** | General-dimensional integer matrix fibre theorem, using Smith normal form. |
| M3 | **COMPILED** | General corrected EHC theorem; concrete T2/T3 determinants, valuations, and projection polynomials. |
| M4 | **COMPILED** | Scalar abstract construction for k=2 and k=3, shared-pool Toeplitz tail, and 6804·2^-96. |
| M5 | **COMPILED** | Sharp B₂(h), overlapping-table conditioning, byte parsing, broadcast lanes, literal flat key addresses, and normalized Style bound in the explicit abstract model below. |

## Reproduction and trust

- Lean: `leanprover/lean4:v4.24.0`.
- Mathlib: `v4.24.0`, commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- Base ProvenHashes commit: `e70213feed3dac6280fe8d7ecdc35dcfd0cf1cc8`.
- The new worktree was copied from `~/agents/lean-hash`, including its `.lake`
  cache and Lean installation. The original worktree was not edited.
- All resume-2 builds and Lean checks use `nice -n 10`, `taskset -c 88-95`,
  and `LEAN_NUM_THREADS=8`. Both build scripts and the remote `env.sh` enforce
  the new allocation. Earlier M1–M4 checkpoints used the original allocation.
- Probabilities are exact nonnegative rationals: cardinality of the event divided
  by cardinality of the finite, uniform key space. Function key spaces give
  independent uniform entries; product key spaces give independent stages.

```bash
cd ~/agents/lean-halftime
source env.sh
bash lean/build-halftime.sh
bash lean/build.sh
```

[HalftimeAudit.lean](lean/HalftimeAudit.lean) explicitly runs `#check @name` and
`#print axioms name` for every new theorem/lemma. The complete elaborated
signatures and per-theorem axiom lists are in
[HalftimeAudit.txt](lean/HalftimeAudit.txt). The audit allows only `propext`,
`Classical.choice`, and `Quot.sound`; some finite certificates use no axioms.
It rejects placeholders, custom axioms, unsafe declarations, and native
computation proofs. The integer certificates use kernel-checked `decide` and
`norm_num`. [FullAudit.txt](lean/FullAudit.txt) covers the 57 inherited proofs.
The scripts fail if a declaration lacks its axiom report.

Final verification: `lake build` passed (7384 jobs, mostly cached), all **237 new
proof declarations** passed their axiom audit, and all **57 inherited proof
declarations** passed the base audit. There are no proof placeholders or added
axioms. Logs: [HalftimeVerification.txt](lean/HalftimeVerification.txt) and
[BaseVerification.txt](lean/BaseVerification.txt).

Proof checkpoints (committed in the isolated Xeon worktree):

| Checkpoint | Commit |
|---|---|
| M2, initial integer NH and forest proofs | `32520551825a5ea4fb8d9c23632f88d5a63eb5d2` |
| M1 complete and M3 core/certificates | `e29040eff70f694b045f2db92c7fca6a8770b342` |
| M4 complete, concrete subset bounds, 127-proof audit | `ac26ea51fa8f221d150eaa49f6730ba65be3aa02` |
| M5 abstract Style model, normalized theorem, 237-proof audit | `0f9aabf3c3fcb08470e30a7f42f16270f028e128` |

The final proof checkpoint also rebuilds and audits M1–M4. The status document
is committed separately after these proof checkpoints, avoiding a self-referential
commit hash in its own contents.

## M1 — COMPILED

Sources: [IntegerNH.lean](lean/ProvenHashes/Halftime/IntegerNH.lean),
[Truncation.lean](lean/ProvenHashes/Halftime/Truncation.lean),
[SharpTruncation.lean](lean/ProvenHashes/Halftime/SharpTruncation.lean).

`nh` adds in `ZMod q`, takes the unsigned representatives of those sums,
multiplies them, and sums in `ZMod (q*q)`. The proof handles both wrap branches.
`nh_adu` proves the stronger arbitrary-radix result `1/q`; `nh32_adu` has the
paper's actual word and output rings:

```lean
theorem nh32_adu {n : ℕ} (x y : Fin n × Bool → ZMod (2 ^ 32))
    (hxy : x ≠ y) (t : ZMod (2 ^ 64)) :
    uniformProb (fun k => nh32 x k - nh32 y k = t) ≤ 1 / (2 : ℚ≥0) ^ 32

theorem nh_mod62_adu {n : ℕ} (x y : Fin n × Bool → ZMod (2 ^ 32))
    (hxy : x ≠ y) (c : ZMod (2 ^ 62)) :
    uniformProb (fun k => lowBits 62 (by decide) (nh32 x k - nh32 y k) = c) ≤
      2 / (2 : ℚ≥0) ^ 32
```

`lowBits` is the canonical ring reduction. The second statement is exactly the
fourth review's residue event, for distinct equal-pair-count messages and every
target. `truncatedNH62Bound` proves the named proposition
`TruncatedNH62Bound`; it is not an additional axiom. The direct proof splits
an exposed key into two intervals, and handles top-bit-only differences
separately. `nh_mod63_adu` also establishes the requested 2ε bound modulo 2^63.
`nh_mod62_coarse` remains available under its explicit weaker name.

`nhLast (x,a) k = nh x k + a`, with an arbitrary unhashed 64-bit accumulator
when q=2^32. Exact scope:

- `nhLast_au`: whole messages distinct ⇒ collision probability ≤1/q.
- `nhLast_adu`: hashed portions distinct ⇒ every difference atom ≤1/q.
- `nhLast_same_hashed_target_probability`: when only the accumulator changes,
  its prescribed difference has probability 1. Thus an all-target AΔU claim
  for this variant on *all* distinct messages would be false.

Remaining M1 statement: **none within this mathematically valid scope**.
Commit: `e29040eff70f694b045f2db92c7fca6a8770b342`.
Axioms: only the three standard Lean axioms listed above; exact lists in audit.

## M2 — COMPILED

Source: [MatrixFibre.lean](lean/ProvenHashes/Halftime/MatrixFibre.lean).
The proof uses Mathlib's Smith normal form for submodules over the PID ℤ,
constructs unimodular row/column transformations, reduces them modulo 2^m,
and counts the diagonal kernels. It works in arbitrary finite dimension;
there is no restriction to r≤3.

Main declaration: `matrix_fibre_card`. Its hypotheses are an integer square
matrix `A : Matrix (Fin r) (Fin r) ℤ`, `A.det ≠ 0`,
`padicValNat 2 A.det.natAbs = τ`, `τ < 64`, a target vector `b`, and existence
of one preimage. Its conclusion is exactly

```lean
Nat.card {x : Fin r → ZMod (2 ^ 64) //
  (A.map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec x = b} = 2 ^ τ
```

The nonzero determinant hypothesis expresses finite 2-adic valuation: Mathlib's
`padicValNat 2 0` is conventionally 0, so it must not be used to represent the
valuation of zero here. `matrix_kernel_card` and `matrix_fibre_card_le` work
modulo 2^m with valuation ≤m; the latter includes empty fibres.

Remaining M2 statement: **none**.
Commit: `32520551825a5ea4fb8d9c23632f88d5a63eb5d2`.
Axioms: only the three standard Lean axioms; exact lists in audit.

**General M2 signature:**

```lean
theorem matrix_fibre_card {r τ : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hA : A.det ≠ 0) (hτ : padicValNat 2 A.det.natAbs = τ) (h64 : τ < 64)
    (b : Fin r → ZMod (2 ^ 64))
    (hb : ∃ x, (A.map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec x = b) :
    Nat.card {x // (A.map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec x = b} = 2 ^ τ
```

## M3 — COMPILED

Sources: [EHC.lean](lean/ProvenHashes/Halftime/EHC.lean),
[Matrices.lean](lean/ProvenHashes/Halftime/Matrices.lean),
[Projections.lean](lean/ProvenHashes/Halftime/Projections.lean).

`ehc_adu` assumes only a distance-r encoder and nonzero r-column minors with
2-adic valuation at most t≤64. It proves, for every distinct input pair and
vector target,

```lean
uniformProb (fun k => ehc encode T x k - ehc encode T y k = b) ≤
  (2 : ℚ≥0) ^ t / 2 ^ (32 * r)
```

Each encoded symbol has an independent *integer* NH key. The proof splits the
whole key space into selected and unselected columns, conditions on every
unselected symbol key, and applies the exact matrix fibre count. It never
assumes independence of output coordinates.

The explicit matrices are:

```text
T2 = [1 0 1 1 2 1 4; 0 1 1 2 1 4 1]
T3 = [0 0 1 4 1 1 2 2 1;
      1 1 0 0 1 4 1 2 2;
      1 4 1 1 0 0 2 1 2]
```

`T2_minors` and `T3_minors` check all 21 and 84 increasing column sets by
`decide`: determinants are nonzero and not divisible by 8. Explicit determinant
formulas are proved equal to `Matrix.det`. Separate certificates cover column
permutations, and `T2_minor_valuations` / `T3_minor_valuations` give the valuation
statements for arbitrary embeddings. The worst valuation 2 is attained by
checked determinants 4 and 12. `ehc_T2_adu` gives 2^-62 and `ehc_T3_adu` 2^-94.

`coefficient2` / `coefficient3` are the minimum square-minor kernel costs for
each row subset (empty-set coefficient 1). `projection_polynomial_T2` and
`projection_polynomial_T3` prove the literal powerset-sum inequalities for all
u,v in ℚ≥0, with t=2:

```text
Σ_S c(S,F) u^(k-|S|) v^|S| ≤ (u+v)^(k-1) (u+4v).
```

Zero minors use the sentinel cost 2^64; the concrete coefficient certificates
ensure that a nonzero minor with smaller cost is always available. The
singleton/pair/full coefficient bounds are (5,4) for T2 and (6,9,4) for T3.
`T2_subset_bounds` / `T3_subset_bounds` additionally derive the corresponding
actual joint probabilities by conditioning and minor selection.

Remaining M3 statement: **none for the requested concrete matrices**. This
is not a general-matrix projection-polynomial theorem for arbitrary k.
Core commit: `e29040eff70f694b045f2db92c7fca6a8770b342`.
Joint probability corollaries: `ac26ea51fa8f221d150eaa49f6730ba65be3aa02`.
Axioms: only the three standard Lean axioms; exact lists in audit.

**General M3 signature:**

```lean
theorem ehc_adu {X I : Type*} [Fintype I] [DecidableEq I] {r n t : ℕ}
    (encode : X → I → (Fin n × Bool → ZMod (2 ^ 32)))
    (T : Matrix (Fin r) I ℤ) (ht : t ≤ 64)
    (hminor : ∀ j : Fin r ↪ I,
      (T.submatrix id j).det ≠ 0 ∧ padicValNat 2 (T.submatrix id j).det.natAbs ≤ t)
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin r ↪ I, ∀ i, encode x (j i) ≠ encode y (j i))
    (x y : X) (hxy : x ≠ y) (b : Fin r → ZMod (2 ^ 64)) :
    uniformProb (fun k => ehc encode T x k - ehc encode T y k = b) ≤
      (2 : ℚ≥0) ^ t / 2 ^ (32 * r)
```

## M4 — COMPILED

Sources: [Forest.lean](lean/ProvenHashes/Halftime/Forest.lean),
[EndToEnd.lean](lean/ProvenHashes/Halftime/EndToEnd.lean),
[Toeplitz.lean](lean/ProvenHashes/Halftime/Toeplitz.lean),
[WordPacking.lean](lean/ProvenHashes/Halftime/WordPacking.lean),
[Construction.lean](lean/ProvenHashes/Halftime/Construction.lean).

`tree_collision_bound` and `forest_collision_bound` prove hε, selecting a
differing subtree/root without assuming independence among nodes at a height.
`forest_final_adu` proves (h+1)ε after independent final compression. The
concrete EHC subset bounds are then fed into the conditional product expansion;
no subset-probability assumption remains in the final construction theorem.

`triangular_adu` is a general fresh-coordinate counting lemma.
`toeplitzNH_adu` proves ε^k AΔU for all vector targets with a pool of overlapping
NH keys. Output j shifts by j **whole NH pairs**. The last differing pair gives
one injective exposed half-word key for each successive output, and previous
outputs ignore that key. `halftimeCore_different_tail` conditions on all prefix
keys and obtains ε^k directly; it adds no tail error. `halftimeCore_equal_tail`
proves exact cancellation of common tails. With no EHC groups, distinct inputs
have differing tails, so the ε^k tail result applies.

### Exact abstract model

The checked final model is the scalar-word construction, with 64-bit words and
these explicit objects:

1. A key-independent forest schedule `s : Fin roots → TreeShape (nt+1) h`.
   Shapes have leaf, node, and skip constructors. Skip permits shorter roots
   within one common height budget. This covers forests of complete f-ary
   trees; the bound holds for every such fixed schedule.
2. Each message is a pair of forest leaf values and a padded tail:
   `((i : Fin roots) → TreeInput X (s i)) × (Fin l × Bool → ZMod (2^32))`.
   Both messages use the same public schedule and padded tail length.
3. A distance-k encoder `X → Fin N → (Fin n × Bool → ZMod (2^32))`, with
   `(k,N)=(2,7)` or `(3,9)`. EHC uses the literal T2/T3 matrices and integer NH.
4. A whole independent NH key per encoded symbol, **reused at every leaf**.
   Each output component has independent tree and final keys. One tree key is
   reused by all nodes at the same height; distinct heights have independent
   keys. Tree nodes hash the first nt child words and carry the last word as
   the unhashed accumulator. Final NH hashes the root list.
5. `packTree` and `packWords` use actual unsigned low/high 32-bit halves, with
   injectivity proved in `WordPacking.lean`. The separately keyed tail uses
   exactly l+k−1 pair keys when l,k>0, shared by its shifted outputs.
6. The result is the componentwise sum modulo 2^64 of forest-final NH and the
   Toeplitz tail. The full key is uniform on the finite product of the EHC,
   component tree/final, and tail key spaces.

No collision-probability or independence-of-derived-outputs hypothesis remains
in `scalar_halftime_two_bound`, `scalar_halftime_three_bound`, or
`scalar_halftime_6804`. Their substantive hypothesis is the specified encoder
symbol distance; the forest schedule and fixed-layout input domain are explicit
parameters. The more general `halftimeCore_*_nh_bound` theorems also support
arbitrary injective tree/final word packings.

For both concrete matrices t=2. The final statements hold for every difference
target, hence in particular for collision target zero:

```text
k=2: Pr ≤ min{1, 2^-64 (h+2)(h+1+2^2)}.
k=3: Pr ≤ min{1, 2^-96 (h+2)^2(h+1+2^2)}.
```

The exact signature of the concrete numerical corollary is:

```lean
theorem scalar_halftime_6804 {X : Type*} {n nt roots l : ℕ}
    (encode : X → Fin 9 → (Fin n × Bool → ZMod (2 ^ 32)))
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin 3 ↪ Fin 9, ∀ i, encode x (j i) ≠ encode y (j i))
    (s : Fin roots → TreeShape (nt + 1) 16)
    (x y : (∀ i, TreeInput X (s i)) × (Fin l × Bool → ZMod (2 ^ 32))) (hxy : x ≠ y)
    (b : Fin 3 → ZMod (2 ^ 64)) :
    uniformProb (fun k =>
      halftimeCore encode T3 (fun _ => nhNode packTree) (fun _ key v => nh32 (packWords v) key) s x k -
      halftimeCore encode T3 (fun _ => nhNode packTree) (fun _ key v => nh32 (packWords v) key) s y k = b) ≤
      6804 / (2 : ℚ≥0) ^ 96
```

Thus `scalar_halftime_6804` is an end-to-end theorem, not merely the numeric
identity `numeric_6804` or the older conditional
`collision_6804_from_subsets`. The latter remain useful intermediate lemmas.

Remaining M4 statement: **none for this documented scalar-word abstract
construction and the requested concrete matrices**. This does not formalize
byte parsing, SIMD lane assembly/horizontal reduction, the implementation's
forest scheduler, an actual distance-3 XOR encoder, the C++ header, or a public
Style wrapper. In particular, it cannot be applied to the shipped `Encode3`
without the distance hypothesis, which the reviews reject for that code.

Commit: `ac26ea51fa8f221d150eaa49f6730ba65be3aa02`.
Axioms: `[propext, Classical.choice, Quot.sound]` for the final bounds;
individual helper lists are in the audit.

## M5 — COMPILED for the specified abstract flat-address model

Sources: [Wrapper.lean](lean/ProvenHashes/Halftime/Wrapper.lean),
[Survival.lean](lean/ProvenHashes/Halftime/Survival.lean),
[SharpT2.lean](lean/ProvenHashes/Halftime/SharpT2.lean),
[StyleCore.lean](lean/ProvenHashes/Halftime/StyleCore.lean),
[Encoding.lean](lean/ProvenHashes/Halftime/Encoding.lean),
[StyleLanes.lean](lean/ProvenHashes/Halftime/StyleLanes.lean),
[StyleLayout.lean](lean/ProvenHashes/Halftime/StyleLayout.lean),
[StyleBytes.lean](lean/ProvenHashes/Halftime/StyleBytes.lean),
[Normalization.lean](lean/ProvenHashes/Halftime/Normalization.lean),
[StyleModel.lean](lean/ProvenHashes/Halftime/StyleModel.lean), and
[StyleSchedule.lean](lean/ProvenHashes/Halftime/StyleSchedule.lean).

### Exact abstract model and its boundary

The theorem concerns the following mathematical family. It does not claim
bit-for-bit equality of its default leaf ordering with the C++ implementation,
or a refinement proof for the C++ scheduler or instruction set.

1. The lane count satisfies `0 < b ≤ 8`, including the shipped widths
   `b = 1, 2, 4, 8`. A message is an actual byte vector with its byte length:
   `StyleMessage b = (N : Fin (144*b*19173961)) × (Fin N.val → Fin 256)`.
   Thus both messages individually lie in the review's sentinel-safe domain.
   `styleByteLimits` checks the four limits 2,761,050,384; 5,522,100,768;
   11,044,201,536; and 22,088,403,072 bytes.
2. There are `floor(N/(144b))` complete leaves. The `lazyHeights` recurrence
   specifies the low-level-first bijective-base-eight root counts, with digit
   `((n-1) mod 8)+1` and recursive quotient `(n-1)/8`. Each root is a complete
   eight-ary tree. Short roots use `skip` to fit a common height budget without
   extra hashing. Lean proves that the leaf count is exactly n, there are at
   most 64 roots, and the maximum live height is at most 7. The next array
   level is reserved for the zero sentinel in this mathematical specification.
3. Leaf ordering is any fixed, key-independent bijection from input groups
   to forest leaves. `byteStyleHash_normalized` holds for every admissible
   public schedule family and every such ordering. The fully instantiated
   helper `modeledStyleHash` uses `Fintype.equivOfCardEq` to choose one ordering.
   This choice is explicit: the helper is not a C++ output-compatibility test.
   The bound is independent of that choice. No scheduler invariant is a
   probability assumption, and the instantiated helper discharges all its
   schedule invariants with the checked bijective-base-eight construction.
4. Input words are loaded little endian. A leaf uses six triples of blocks,
   in symbol/triple/lane order. `encode2` retains the six symbols and appends
   their bitwise XOR, with distance two proved for arbitrary bit patterns.
   Integer NH and the literal T2 matrix act independently on each physical
   lane, while EHC keys are broadcast across lanes and reused across leaves.
5. Tree nodes carry child zero unchanged and hash children 1–7. Each height
   and output component has its own keys, broadcast across lanes and reused
   across nodes. Final NH uses independent keys per root, component and lane;
   flattening implements the horizontal sum modulo 2^64. No independence of
   derived components or physical lanes is assumed.
6. For remainder r, the parser inserts `floor(r/(8b))+1` raw blocks, including
   an extra zero block when r is aligned. The last block is zero padded.
   Equal-length parsing is proved injective. The two tail outputs share a
   pool with offsets 0 and b **whole NH pairs**. The differing-tail bound is
   ε² after conditioning on every prefix key; there is no additive tail term.
7. Keys are independent uniform 64-bit words represented by `XorWord 64`.
   The relevant flat array has 6144 words. Additional unused allocation words
   integrate out by `uniformProb_restrict`. The modeled absolute core reads
   are exactly:

   ```text
   EHC:       512 + 3*symbol + triple
   tree:      533 + 14*level + 7*component + childOffset
   final NH:  659 + b*(2*root + component) + lane
   tail pool: 659 + 2*b*roots + pairOffset
   ```

   `styleWordAddressNat_injective` proves that the distinct stage slots use
   distinct addresses. `styleWordAddressNat_lt` proves all reads are below
   2048, and `readStyleKey_uniform` derives the structured independent key
   distribution from the actual flat table. The address envelope is
   `659+b*(2*roots+19) ≤ 1835`. Intentional sharing within EHC/tree instances
   and the Toeplitz tail is retained.
8. The wrapper XORs eight length-byte lookups at addresses `256*j+byte_j(N)`
   and sixteen output-byte lookups at `2048+256*j+byte_j(core)`. The length
   table and core use the same lower words. All output-table entries are
   independent of those lower words. The length encoding is injective on
   the verified byte domain. All messages and schedules are fixed before
   the uniform key is sampled.

This formalizes the abstract unsigned-arithmetic and flat-address contract,
including byte input and the entropy overlap. It does not establish portable
ISO-C++ behavior for the header's undersized table view, a machine-code
refinement, a PRNG-key guarantee, or safety outside the stated domain.

### Sharp core bound

`nh_T2_sharp_subset_bounds` derives the singleton sum ≤3ε and joint bound
≤2ε² from integer NH and M1's sharp mod-2^62 result. `T2_four_witness` and
the finite coefficient certificates are kernel checked. The survival proof
retains the factors from earlier stages, giving

```text
ε = 2^-32,  s_h = (1-ε)^(h+1),  a_h = 1-s_h,
B₂(h) = (a_h+s_h*ε)(a_h+2*s_h*ε) ≤ (h+2)(h+3)*2^-64.
```

`styleTwoBound_formula` proves the displayed identity. `styleForest_survival`,
`styleCore_survival`, `flatStyleCore_survival`, and `byteStyleCore_survival`
successively discharge the actual lane operations, tail, flat key extraction,
and byte parser. The byte-level signature is:

```lean
theorem byteStyleCore_survival {b bytes : ℕ} (hb0 : 0 < b) (hb : b ≤ 8)
    (plan : StyleSchedule (styleGroups b bytes))
    (x y : Fin bytes → Byte) (hxy : x ≠ y) (target : Fin 2 → Word64) :
    uniformProb (fun key =>
      byteStyleCore hb0 hb plan x key - byteStyleCore hb0 hb plan y key = target) ≤
      styleTwoBound (1 / (2 : ℚ≥0) ^ 32) plan.height
```

The no-group case gets the sharper ε² bound in `byteStyleCore_no_groups`.
`byteStyleCore_word_cap` proves the core bound `L/2^64` using the checked
inequality `(h+2)(h+3) ≤ 18*8^h` and the number of bytes in complete leaves.

### Exact wrapper conditioning and normalized theorem

`wrapper_conditioning` permits arbitrary dependence between the core and
length term. It proves `δ Pr[Fx≠Fy] + Pr[Fx=Fy ∧ lengthTerm_x=lengthTerm_y]`.
The equal-length specialization is exactly:

```lean
theorem flat_wrapper_equal_length
    (x y : LowerTableKey → Fin 16 → Fin 256)
    (lengthBytes : Fin 8 → Fin 256) :
    uniformProb (fun key =>
      flatStyleWrapper x lengthBytes key = flatStyleWrapper y lengthBytes key) =
      (1 / (2 : ℚ≥0) ^ 64) + (1 - 1 / (2 : ℚ≥0) ^ 64) *
        uniformProb (fun k => x k = y k)
```

`byteStyleHash_equal_length` specializes this to the byte-level core.
`byteStyleHash_unequal_length` proves the bound `2^-63-2^-128` from the
marginal length-table collision probability, without an independence
assumption between length terms and core outputs.

The final instantiated theorem has no assumed encoder distance, collision
bound, parser injectivity, key independence, address disjointness, or schedule
invariants. L is a positive cap in **eight-byte words**:

```lean
theorem modeledStyleHash_normalized {b : ℕ} (hb0 : 0 < b) (hb : b ≤ 8)
    (L : ℕ) (hL : 1 ≤ L) (x y : StyleMessage b) (hxy : x ≠ y)
    (hx : x.1.val ≤ 8 * L) (hy : y.1.val ≤ 8 * L) :
    uniformProb (fun key => modeledStyleHash hb0 hb x key = modeledStyleHash hb0 hb y key) ≤
      (L : ℚ≥0) * (1 / 2 ^ 63 - 1 / 2 ^ 128)
```

`byteStyleHash_normalized` is the more general version for every admissible
public schedule family. Thus the instantiated result is an actual finite-key
probability theorem about byte messages, rather than only an arithmetic
inequality or a reduction assuming a core probability bound.

Remaining M5 statement: **none for the abstract model just specified**.
An operational refinement connecting the C++ DFS loop and its exact leaf
ordering to this model is outside the claim. The optimality witness for the
coefficient was not requested as a Lean milestone and is not formalized.
Proof commit: `0f9aabf3c3fcb08470e30a7f42f16270f028e128`.
Final bounds use `[propext, Classical.choice, Quot.sound]`; all individual
signatures and axiom lists are in [HalftimeAudit.txt](lean/HalftimeAudit.txt).

## Input provenance

The mathematical inputs were the two review summaries, `PROOF.md`, `VERDICT.md`,
`referee_RESULT.md`, and the certificates under `review-support/`. The header
was read as context and was not modified. In particular, the assumed distance-3
encoder in the abstract theorem does **not** certify the shipped `Encode3`.

SHA-256 fingerprints:

```text
PROOF.md
2695053e8af2b907d43784f8bae1ac44a6fb78be6992ca031dc59b7c088df44d
second_review_summary.md
add0b1151dbec05d08014a15cb5115b9e7f2fcd1c0c1239200e5fd2dddb1f1e2
fourth_review_summary.md
e64bf8069e00ea12cfaa67e24de04eee78e8f79057821cbb7ada3aba5408698d
halftime-current.hpp
7ef5dd48f54537b430f85bc1867b23a93551ab1c56415cfcef362d1651956cc3
```
