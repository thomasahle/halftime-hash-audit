# HalftimeHash: collision-bound audit, repaired proof, and implementation checks

Companion artifacts for https://github.com/jbapple/HalftimeHash/issues/3 (and the NEON dispatch fix in PR #2).
Everything here concerns the paper *HalftimeHash: Modern Hashing without 64-bit Multipliers or Finite Fields*
(arXiv:2104.08865) and the header `halftime-hash.hpp` at commit `caf7924ceab4721f4e0cc33442b185558ba7f1c4`
(sha256 `7ef5dd48f54537b430f85bc1867b23a93551ab1c56415cfcef362d1651956cc3`).

**Method note.** The analysis was machine-assisted: several independent automated passes wrote the proofs and
harnesses, and each result was then re-derived by a separate pass, executed against the unmodified header, or checked
in Lean. Nothing here is taken on trust from a single pass; the referee report and the execution report were produced
by agents that did not see each other's code. Corrections are welcome as issues here or on the HalftimeHash tracker.

## Contents

- `proof/` — `PROOF.md`: the 63-bit certificate for the shipped `HalftimeHashStyle64/128/256/512` wrappers (key overlap
  handled by conditioning; finite length caps), the corrected `Encode2` core bound, and the `Encode3`/24-byte-core
  refutation; `VERDICT.md`, `SUMMARY.md`; `REFEREE_REPORT.md`: an adversarial re-derivation of every step
  (key layout recomputed from the header, all 21 minors by Smith normal form, the sharpest overlap witness).
- `certificates/` — exact integer certificates: the 21 two-column minors of the 2×7 combine matrix and the 84
  three-column minors of the 3×9 matrix with their 2-adic valuations, the `Encode3` distance witness (compiled from
  the fetched header), layout and stack-boundary diagnostics, generating scripts.
- `execution/` — `RESULT.md`: the independent execution check (pooled ε = 2^-31.95 over 2^38.2 uniform key arrays for
  the 24-byte witness; conditioning tests; overlap search on the Style wrappers; guard-page key read-set; breakpoint
  evidence that the Style wrappers never call `Encode3`), with the harness sources and logs under `harness/`.
- `lean/` — a Lake project (Lean 4.24.0, Mathlib v4.24.0) with the repaired theorem for the intended construction
  machine-checked: integer NH almost-Δ-universality (including the truncated mod 2^62 form), the matrix-fibre lemma via
  Smith normal form, the corrected EHC theorem and the projection-polynomial lemma with the T2/T3 minors certified by
  decision procedures, the forest lemma and the end-to-end bound 2^-32k(h+2)^(k−1)(h+1+2^t) with the 6804·2^-96
  corollary, and the flat-address model of the Style wrappers with the normalized bound. `STATUS.md` lists every
  theorem, its axioms, and the build commands.
- `reviews/` — the two full audit passes (`AUDIT_full.md`, `AUDIT_REVIEW_full.md`; HalftimeHash is §7 and §3
  respectively) and condensed summaries of two further independent reviews of the paper.
- `drafts/` — a draft write-up, `halftime_repair_DRAFT.pdf`, assembling the above; `DRAFT_NOTES.md` lists what is still
  marked as unsourced in it. Not yet reviewed; numbers trace to the files above.

## The short version

1. The published proof does not hold as written (Lemma 3 multiplies component collision probabilities without knowing
   every component differs; Theorem 1 confuses p with its exponent and omits a division), but the intended construction
   is repairable: with a distance-k encoder and independent stage keys, Pr[collision] ≤ 2^-32k (h+2)^(k−1)(h+1+2^t),
   which recovers the ">83 bits" headline (83.27 bits at h = 16) for HalftimeHash24. Machine-checked in `lean/`.
2. The shipped `Encode3` has packet distance 1 (the `DistributeRaw` lambda captures `iter` by value), so the public
   24-byte functions `advanced::Vj<3>` admit a fixed pair with collision probability ≥ 2^-32; measured 2^-31.95.
3. The shipped 64-bit Style wrappers are fine: 63 bits in the length-normalized metric, ε ≤ L(2^-63 − 2^-128) with the
   coefficient attained, on an explicit finite length domain, for independent uniform key words.
4. Smaller defects: `TabulateAfter`'s undersized table view (UBSan), the NEON dispatch names (PR #2), and
   `GetEntropyBytesNeeded<W,3>` undersizing the key for the 24-byte functions.

## Licence

Code and certificates: MIT. Text: CC BY 4.0. Copyright 2026 Thomas Dybdahl Ahle.
