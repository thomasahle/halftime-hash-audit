# Proven hash collision bounds

Lean 4.24.0 and Mathlib `v4.24.0`, commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

This page describes the inherited base modules. HalftimeHash milestones are
documented in `HALFTIME_README.md` and `../LEAN_HALFTIME_STATUS.md`.
The isolated work directory for this extension is `~/agents/lean-halftime/` on
`thomas-ahle@hardware.normalcomputing.net`. The local copy contains sources and
verification reports, without toolchains, dependency checkouts, or build caches.

On that server:

```bash
cd ~/agents/lean-halftime
source env.sh
cd lean
export LEAN_NUM_THREADS=8
nice -n 10 taskset -c 88-95 lake exe cache get
./build.sh
```

`build.sh` runs `lake build`, prints the main and complete axiom audits to
`Audit.txt` and `FullAudit.txt`, and checks that no local proof uses a placeholder,
a declared axiom, or `native_decide`. All work runs at niceness 10 with CPU
affinity restricted to cores 88–95 and at most eight threads. The server-specific environment keeps elan
and Mathlib's cache inside the permitted workspace; its CA bundle is used for
Mathlib's bundled curl.

- `Probability.lean`: exact finite uniform probability and coordinate counting.
- `Polynomial.lean`: coefficient-vector polynomial hashes, prime fields, GF64.
- `NH.lean`: exact difference-universality of field NH.
- `Tabulation.lean`: exact XOR simple-tabulation universality.
- `Decoder.lean`: the paper's explicit recurrence coefficient decoder.
- `Recurrence.lean`: key-polynomial decoder, recurrence equivalence, and both
  equal-length and arbitrary-length Schwartz–Zippel bounds.
- `Composition.lean`: independent-key composition and conditional ChainHash bounds.
- `MultiplyShift.lean`: two proved reductions and an **unproved proposition**
  recording the full multiply-shift claim. It does not assert that claim.

See `../STATUS.md` for exact theorem statements and limitations. In particular,
polynomial messages need a length qualification; field NH is not integer NH or
unreduced CLNH; and the conditional composition theorems do not discharge the
paper's concrete stream-encoding and finalizer obligations.

`uniformProb E` is the nonnegative rational `#{k | E k}/#K`. Uniform keys in a
full product or function space model independent uniform components.
