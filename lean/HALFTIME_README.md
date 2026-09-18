# HalftimeHash formalization

This extends ProvenHashes using Lean 4.24.0 and Mathlib v4.24.0. Read
`../LEAN_HALFTIME_STATUS.md` for the milestone status and the remaining claims.
The inherited `README.md`, `Audit.lean`, and `FullAudit.lean` describe the base
project; they do not establish the HalftimeHash milestones.

All compilation was performed on `hardware.normalcomputing.net` in
`/home/thomas-ahle/agents/lean-halftime/lean`, using the cache copied from
`/home/thomas-ahle/agents/lean-hash`. The source mirror excludes `.lake`, `.git`,
the Lean installation, and binary artifacts. The Mac only performs editing,
small file operations, and SSH/rsync transport.

Run on the Xeon:

```bash
cd ~/agents/lean-halftime
source env.sh
bash lean/build-halftime.sh
```

The script runs `lake build` with `nice -n 10`, `taskset -c 88-95`, and
`LEAN_NUM_THREADS=8`. It generates `HalftimeAudit.lean` with explicit `#check`
and `#print axioms` commands for every theorem/lemma in each imported Halftime
module. It checks that every declaration has an audit result and that the only
reported axioms are `propext`, `Classical.choice`, and `Quot.sound`. It also
checks all project proof sources for placeholders, custom axioms, unsafe
declarations, and native computation proofs. See `HalftimeAudit.txt` for the
exact signatures and axiom lists, and `HalftimeVerification.txt` for the build
result. `build.sh` separately audits all 57 inherited proof declarations.

Probabilities are exact nonnegative rationals: event cardinality divided by
the cardinality of the finite uniform key space. Function-valued key spaces
model independently uniform entries; product key spaces model independently
keyed stages. No PRNG expansion is assumed to create independent entropy.

The modules are:

- `Probability.lean`: counting, conditioning, coordinate exposure, and products.
- `IntegerNH.lean`: unsigned representative multiplication, wrap-aware NH AΔU,
  and the correctly scoped unhashed-accumulator variant.
- `MatrixFibre.lean`: general integral diagonalization from Mathlib's Smith
  normal form and exact matrix fibre cardinalities modulo powers of two.
- `Matrices.lean`: the explicit combine matrices, exhaustive integer determinant
  certificates, and the concrete projection-polynomial bounds.
- `EHC.lean`: the distance-k encoder theorem, with key-space splitting and
  conditioning on all unselected symbols; concrete T2 and T3 corollaries.
- `Projections.lean`: actual joint subset-probability bounds for the concrete
  matrices, obtained by selecting scalar or square minors and conditioning.
- `Forest.lean`: fixed tree/forest schedules, one shared key per height, the
  hε root-list bound, and independently keyed final compression.
- `EndToEnd.lean`: conditional component composition from joint subset bounds,
  tail conditioning, and exact numeric arithmetic.
- `Truncation.lean`: exact residue-fibre counts, the mod-2^63 bound, the coarse
  mod-2^62 consequence, and the sharper proposition's definition.
- `SharpTruncation.lean`: the sharp mod-2^62 theorem, proved directly by key
  counting, including the exceptional top-bit-only differences.
- `Toeplitz.lean`: general triangular key exposure and the joint ε^r AΔU bound
  for NH outputs sharing a pool shifted by whole pairs.
- `WordPacking.lean`: injective low/high 32-bit decomposition of 64-bit words,
  root-list packing, and child packing with one unhashed accumulator.
- `Construction.lean`: the explicit scalar-word EHC/forest/final-NH/Toeplitz
  construction and its k=2 and k=3 bounds, including the 6804/2^96 corollary.
- `Wrapper.lean`: exact conditioning with overlapping core/length tables,
  flat table addresses, and equal/unequal length reductions.
- `Survival.lean`, `SharpT2.lean`, `StyleCore.lean`: sharp T2 subset bounds
  from truncated NH and the B₂(h) survival formula.
- `Encoding.lean`: unrestricted XOR parity distance for the actual Encode2.
- `StyleLanes.lean`: broadcast EHC/tree keys, independent finalizer lane keys,
  and the shared tail pool shifted by b whole pairs.
- `StyleLayout.lean`: literal core addresses, their injectivity and range,
  and uniform structured keys derived from the lower flat table.
- `StyleBytes.lean`: little-endian loading, zero padding and injective parsing.
- `Normalization.lean`, `StyleModel.lean`: the positive word-cap bound and
  normalized wrapper theorem for every admissible public schedule.
- `StyleSchedule.lean`: the bijective-base-eight abstract forest, its checked
  stack bounds, and the instantiated `modeledStyleHash_normalized` theorem.

The final construction theorems use a distance-k encoder, a fixed public forest
shape, equal padded tail lengths, independent stage/component keys, and scalar
64-bit words. They allow EHC key reuse across all leaves, tree key reuse across
all nodes at a height, and overlapping Toeplitz tail keys. The concrete packing
corollaries assume no hash collision bound. Encoder distance is a structural
hypothesis and is not a claim about the shipped `Encode3` implementation.
M5 separately verifies the abstract Style family with byte input, literal flat
addresses and table overlap. Its final bound is L(2^-63-2^-128), for the exact
stack-safe byte domains and the independent uniform entropy model. The general
theorem permits every fixed public leaf ordering; the instantiated helper
chooses one using a finite equivalence. No bit-for-bit equality with the C++
DFS ordering or ISO-C++/machine-code refinement is claimed. The full model and
boundary of the claim are explicit in `../LEAN_HALFTIME_STATUS.md`.

Final proof checkpoint: `0f9aabf3c3fcb08470e30a7f42f16270f028e128`.
`lake build` passed (7384 jobs); all 237 Halftime declarations and 57 inherited
declarations passed the axiom audits. M1–M5 are COMPILED within their stated
abstract scopes.
