# Fourth HalftimeHash review (author-run, 2026-09-18): repaired paper theorem + code-level bounds at caf7924 — condensed
PART 1 (intended construction, distance-k encoder, independent stage/component keys; EHC keys may be reused across
instances/lanes, tree keys per height, final NH keys per component/root position; tail: separate Toeplitz pool):
- Matrix-fibre lemma (Smith normal form over Z): |ker A| = 2^{v2(det A)} on (Z/2^64)^r; EHC is 2^{t−32k}-AΔU with
  t = max_F v2(det T_F) (441 minors rechecked with two determinant algorithms; t = 2,2,3,3).
- Projection-polynomial lemma: Σ_S c_{S,F} u^{k−|S|} v^{|S|} ≤ (u+v)^{k−1}(u + 2^t v) (column operations to
  upper-triangular B = AV, Cauchy–Binet, concentration inequality) — general, not matrix-specific enumeration.
- Forest specified as complete f-ary trees over the base-f digits of N; one-component lemma: root lists agree w.p.
  ≤ hε; tree+final NH (h+1)ε-AΔU.
- End-to-end: Pr ≤ min{1, 2^{-32k}(h+2)^{k−1}(h+1+2^t)}; tail handled by conditioning (no additive term); no EHC group:
  ε^k.  HalftimeHash24: 6804·2^-96 → 83.27 bits at h = 16.  Explicit XOR encoders with 289 exact rank checks.
  Resource formulas: M(L) = b(ew+k)N + kℓ; I(L) = ew + k(f−1)h + kbR + (ℓ+k−1)[ℓ>0]; errata as in the third review.
PART 2 (code at commit caf7924ceab4721f4e0cc33442b185558ba7f1c4; independent uniform entropy words; flat-address,
unsigned-arithmetic execution model; stack-safe domain):
- Encode3/4/5: DistributeRaw captures iter by value → all parity packets depend only on the first four raw blocks;
  changing only raw_io[6] changes only systematic packet 2 → packet distance exactly 1.  Encode2 is fine (distance 2).
- Explicit event: zero group vs word 6b = 1 collides iff high32(core word 6) = 0 → Pr ≥ 2^-32 for k = 3, 4, 5 at every
  stack-safe length containing an EHC group (same witness as ours).  Raw 24/32-byte cores: essentially 32 bits.
- Truncated-NH lemma: Pr[NH(x) − NH(y) ≡ c mod 2^62] ≤ 2ε (also mod 2^63) — sharper than 4ε from atoms.
- Distance-2 core: Pr[D1=0] + Pr[D2=0] ≤ 3ε, Pr[D1=D2=0] ≤ 2ε² → B_2(h) = (a_h + s_h ε)(a_h + 2 s_h ε) ≤ (h+2)(h+3)2^-64
  with a_h = 1 − (1−ε)^{h+1}; B_3 = B_4 = ε + a_h ε + (1−2ε)a_h² ≤ 2^-32 + (h+1)(h+2)2^-64; B_5 ≤ (h+2)2^-32.
- Wrapper: keys 0–2047 length tables, 2048–4095 / 4096–6143 output tables; core from word 512, max index 1834 →
  equal lengths: Pr = δ + (1−δ)Pr[F_x = F_y]; unequal lengths ≤ 2δ − δ²; lengths differing in the low 16 bits: exactly δ.
- Actual forest: promotion before insertion → live counts are bijective base-8 digits; h(N) = ⌊log_8(7N+1)⌋ − 1;
  group sizes G_k = 24 d_k b (d_2 = 6, d_3 = d_4 = 7, d_5 = 5).  Stack-safe domain N < (8^9−1)/7 = 19,173,961
  (h ≤ 7, ≤ 64 live roots); Style512 cap n < 22,088,403,072 bytes.
- Uniform stack-safe bounds: raw 16-byte core < 90·2^-64 (57.51 bits); raw 24/32-byte < 2^-32 + 72·2^-64; raw 40-byte
  < 9·2^-32; public Style functions incl. unequal lengths < 91·2^-64 (57.49 bits).
- Normalised theorem: Pr ≤ L(2^-63 − 2^-128), coefficient C = 2 − 2^-64 optimal (0x00 vs 0x01: exactly 2^-63 − 2^-128)
  → 63 bits in the write-up's metric, matching our certificate exactly.
- Raw advanced cores do not encode length: empty input and a one-byte zero input become the same zero-padded tail
  block and collide for EVERY key (fixed-length scope only).  TabulateAfter's undersized array view: theorems describe
  flat-address behaviour, not every ISO-C++ optimisation.
Not yet in our records: the PDFs/TeX/verification packages live in the reviewer's sandbox.
