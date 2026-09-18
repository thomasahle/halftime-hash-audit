# Draft notes

Delivered: `halftime_repair.tex`, `refs.bib`, and the 11-page `halftime_repair.pdf`.
The article is self-contained, with reconstructed proofs, the code execution contract,
three result tables, source citations, and appendices for errata and evidence qualifications.

## Every manuscript TODO

The following list is generated from every `\todo{...}` invocation in the TeX source.
It excludes the macro definition. Five TODOs remain, all concerning missing primary
review or historical execution material; none is silently treated as available.

1. **`halftime_repair.tex:132`** — Obtain the fourth review's full PDF/TeX and verification package; the projection proof here is independently reconstructed from its condensed description, not quoted from an available full proof.

2. **`halftime_repair.tex:225`** — Attach the primary unconditioned sampling logs for the 4/3/5/7 counts and the independent harness package. The supplied filed issue records these totals; the supplied execution report does not contain their detailed result rows.

3. **`halftime_repair.tex:266`** — Obtain the full fourth-review code-bound proof and certificates, including its truncated-NH derivation and reported 289 encoder rank checks. Equations (\ref{eq:b2})--(\ref{eq:b5}) are reconstructed above; the unavailable package has not been inspected.

4. **`halftime_repair.tex:358`** — Obtain the second review's full paper-errata and replacement-bound proof. Its condensed summary is available; its full third-party proof text is not.

5. **`halftime_repair.tex:408`** — Reconcile the execution report's final-section wording with its raw logs, and archive the NEON PR's vector corpus and verification package. The present note uses the detailed conditioning table and does not claim to have rerun the large historical experiments.

## Source conflicts resolved

- `halftime_referee.md` says the parity packets depend on the first six blocks; the filed
  issue also uses a misleading whole-symbol XOR shorthand. The actual symbolic masks are
  `(1,2,4)` and `(3,6,12)`, proving dependence on blocks 0–3. These were rerun against the
  saved header. `Encode4/5` were checked as well.
- `halftime_execution.md` has a concluding “iff” for the full hash and an inconsistent
  claim of conditioned `2^34` trials. The paper uses its detailed `2^20` conditioning
  cells and the rigorous full-hash **lower bound**, following `PROOF.md`.
- The unconditioned counts 4/3/5/7 per `2^34` trials are present in
  `halftime-issue-final.md`. Their detailed result logs are absent here. They are
  attributed historical reports, not measurements rerun for this draft.
- The earlier proof/referee use a valid but looser Encode2 bound and forest-depth upper
  bound. The article derives the fourth summary's sharper truncated-NH bound and exact
  bijective-base-eight depth.
- The matrix-fibre equality includes its necessary valuation restriction; for a general
  integer matrix the exact kernel formula uses capped Smith-invariant valuations.
- Rounded 57.51/57.49-bit pointwise bounds are labelled approximate; the exact
  length-normalised coefficient is stated separately.

## Fresh verification

No packages were installed. The paper was compiled locally using the existing
TeX Live 2023 `pdflatex` and `bibtex`; SSH fallback was unnecessary.

```sh
pdflatex -interaction=nonstopmode -halt-on-error halftime_repair.tex
bibtex halftime_repair
pdflatex -interaction=nonstopmode -halt-on-error halftime_repair.tex
pdflatex -interaction=nonstopmode -halt-on-error halftime_repair.tex
python3 checks/rederive.py > checks/rederive.log
clang++ -std=c++17 -O2 -U__ARM_NEON -U__ARM_NEON__ -fwrapv \
  checks/header-check.cpp -o checks/header-check
./checks/header-check > checks/header-check.log
clang++ -std=c++17 -O2 -U__ARM_NEON -U__ARM_NEON__ -fwrapv \
  checks/symbolic.cpp -o checks/symbolic
./checks/symbolic > checks/symbolic.log
```

The local copy of the supplied harness changes only its include path; the audited header
is unchanged. Fresh results:

- 441 maximal minors, checked by recursive determinants and exact rational elimination;
  maximum valuations 2/2/3/3. All projection coefficient bounds also pass.
- All two-word NH input differences and targets for half-word widths 2 and 3 satisfy
  the truncated-NH bound. The article gives the general proof; small-word execution is
  only a transcription check.
- Actual forest formula checked on 200,000 positive leaf counts, with exact boundary
  checks, key ranges and byte limits.
- Wrapper normalisation comparisons checked by exact rational arithmetic across the
  safe height plateaus. All 28 ranks of the explicit replacement distance-3 encoder pass.
- Real-header scalar harness: PASS, 7,680 key/context cases at each of four widths,
  including 1,280 favourable full collisions per width; Encode2 exhaustive binary
  subalphabet has 262,143 nonzero inputs and minimum symbol distance 2.
- Harness digests reproduce the supplied certificates:
  `4cfca77716c818c2` (witness) and `7a839fa25ab96053` (wrapper).
- Real-header symbolic checks reproduce Encode3 masks and confirm first-four-block
  parity dependence for Encode3/4/5.

`checks/rederived.json`, `checks/header-check.log`, and `checks/symbolic.log` preserve
these results. The billion-key historical experiments and NEON PR corpus were not rerun.
All 11 PDF pages were rendered with Poppler and visually inspected. There are no unresolved
citations, missing references, BibTeX warnings, or overfull boxes. One benign underfull
paragraph remains. Build and rendering logs are in `tmp/pdfs/`.

## Lean status at delivery

Checked `<workspace>/another pass/lean-halftime/LEAN_HALFTIME_STATUS.md` at **2026-09-18T14:03:37+02:00**.

The requested file is absent; Section 6 therefore says **in progress**, as requested.
A differently named `LEAN_STATUS.md` is not treated as the requested final status file.

## Scope

Theorems for the shipped wrappers assume independent uniform entropy words, the specified
flat-address/modular-arithmetic function, the documented ABI, and the explicit finite safe
length domain. The raw-core bounds have equal-length scope. The draft does not certify
arbitrary C++ compiler behaviour, PRNG-expanded keys, or inputs beyond the stack-safe cap.
