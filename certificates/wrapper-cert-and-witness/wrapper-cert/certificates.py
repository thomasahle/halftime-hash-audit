#!/usr/bin/env python3
"""Exact, dependency-free supplements to ../checks.py. No statistical claims."""
import hashlib
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
Q = 1 << 32
R = Q * Q


def valuation(x):
    assert x
    x = abs(x)
    return (x & -x).bit_length() - 1


T = [[1, 0, 1, 1, 2, 1, 4], [0, 1, 1, 2, 1, 4, 1]]
certs = []
for F in itertools.combinations(range(7), 2):
    rows = []
    for S in [(0,), (1,), (0, 1)]:
        choices = []
        for J in itertools.combinations(F, len(S)):
            det = (T[S[0]][J[0]] if len(S) == 1 else
                   T[0][J[0]] * T[1][J[1]] - T[0][J[1]] * T[1][J[0]])
            if det:
                choices.append((valuation(det), J, det))
        v, J, det = min(choices)
        rows.append(dict(rows=S, columns=J, determinant=det,
                         v2=v, kernel_size=1 << v))
    certs.append(dict(differing_columns=F, minors=rows,
                      singleton_sum=rows[0]['kernel_size'] + rows[1]['kernel_size'],
                      full_kernel=rows[2]['kernel_size']))
assert len(certs) == 21
assert max(c['singleton_sum'] for c in certs) == 5
assert max(c['full_kernel'] for c in certs) == 4
(HERE / 'encode2-minors.json').write_text(json.dumps(certs, indent=2) + '\n')

# Exhaust the complete one-bit-per-component alphabet for the systematic code.
# The proof for arbitrary block width is in PROOF.md; this check is independent.
histogram = {}
for x in range(1, 1 << 18):
    symbols = [(x >> (3 * j)) & 7 for j in range(6)]
    parity = 0
    for s in symbols:
        parity ^= s
    weight = sum(s != 0 for s in symbols) + (parity != 0)
    histogram[weight] = histogram.get(weight, 0) + 1
assert min(histogram) == 2

# Bijective base-eight digits are the live stack lengths, lowest first.
def digits(n):
    out = []
    while n:
        n, r = divmod(n - 1, 8)
        out.append(r + 1)
    return out


C8 = sum(8 ** j for j in range(1, 9))
assert digits(C8) == [8] * 8
assert digits(C8 + 1) == [1] * 9
assert digits(8) == [8] and digits(9) == [1, 1]

layout = []
for b in (1, 2, 4, 8):
    end = 512 + 21 + 2 * 7 * 9 + b * (2 * 64 + 18 + 1)
    assert end <= 2048
    limit = 8 * b * 18 * (C8 + 1)
    Lmax = (limit - 1) // 8
    candidates = [(1, 2)]
    for h in range(9):
        L = 18 * b * 8 ** h
        if L <= Lmax:
            candidates.append((L, (h + 2) * (h + 5) + 1))
    # eps(L) = coefficient / 2**64. All plateau minima suffice.
    assert min(Fraction(L, c) for L, c in candidates) == Fraction(1, 2)
    # Sharp envelope: u + (1-u)*(c-1)*u. Exact integer score comparison.
    assert all(L * (2 * R - 1) >= R + (R - 1) * (c - 1)
               for L, c in candidates)
    assert all(Fraction(18 * b * 8 ** h, (h + 2) * (h + 5)) >= 1
               for h in range(9))
    layout.append(dict(style=64 * b, lanes=b, leaf_bytes=144 * b,
                       max_complete_leaves=C8, exclusive_byte_limit=limit,
                       largest_integer_word_cap=Lmax,
                       core_word_start=512, finalizer_word_start=659,
                       core_word_end_exclusive=end,
                       output_table_word_start=2048,
                       score_bits=63, score_candidates=candidates))

# Exact fibre count for the Encode3 witness, not an estimate:
# a = low32(K[6]), z = high32(K[6]); input word 6 changes 0 -> 1.
# a < Q-1: delta = z.  a == Q-1: delta = -(Q-1)z (mod Q**2).
# In both branches the multiplier is odd, so its only zero on 0 <= z < Q is 0.
fibres = []
for a_count, delta_factor in [(Q - 1, 1), (1, -(Q - 1))]:
    gcd = math.gcd(delta_factor, R)
    assert gcd == 1
    # All solutions to c*z=0 mod R are multiples of R/gcd.
    z_count = (Q - 1) // (R // gcd) + 1
    assert z_count == 1
    fibres.append(dict(low_half_count=a_count, difference_factor=delta_factor,
                       gcd_with_2pow64=gcd, high_half_zero_count=z_count,
                       colliding_word_keys=a_count * z_count))
count = sum(f['colliding_word_keys'] for f in fibres)
assert count == Q
lower = Fraction(count, R)
advertised_at_h0 = Fraction(65, 1 << 96)
assert lower > advertised_at_h0

# Also exhaust smaller analogues of precisely the same identity, all low/high keys.
small_fibres = []
for w in range(1, 9):
    q = 1 << w
    n = sum((a * z - ((a + 1) % q) * z) % (q * q) == 0
            for a in range(q) for z in range(q))
    assert n == q
    small_fibres.append(dict(half_bits=w, total_keys=q * q, collisions=n))

entropy_h = 0
x = ((1 << 64) - 1) // (8 * 6 * 3)
while x >= 8:
    entropy_h += 1
    x //= 8
entropy_words = 6144 + 21 + 14 * entropy_h + 128 * entropy_h + 144 + 1

result = dict(
    sources={p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
             for p in ['halftime-current.hpp', 'halftime-current.tex', 'AUDIT_REVIEW.md']},
    encode2=dict(matrix=T, distance=2, exact_binary_codeword_weight_histogram=histogram,
                 nonzero_codewords=sum(histogram.values()), minor_certificates=21,
                 max_singleton_kernel_sum=5, max_full_kernel=4,
                 core_bound='2^-64 below a leaf; (h+2)(h+5)2^-64 otherwise'),
    layout=layout,
    entropy_words=entropy_words,
    entropy_bytes=entropy_words * 8,
    encode3_witness=dict(zero_message=True, differing_word_index='6*b',
                         new_word_value=1, byte_length='168*b',
                         key_condition='high32(core_key[6]) = 0',
                         key_word_fibres=fibres,
                         ehc_collision_probability=str(lower),
                         full_core_collision_probability_lower_bound=str(lower),
                         full_core_probability_is_not_claimed_exact=True,
                         claimed_paper_bound_at_h0=str(advertised_at_h0),
                         lower_bound_to_claim_ratio=str(lower / advertised_at_h0),
                         small_word_exact_checks=small_fibres),
    short_wrapper_pair=dict(byte_length=1, messages=['00', '01'],
                            core_collision_probability=str(Fraction(1, R)),
                            exact_wrapper_collision_probability=str(Fraction(2, R) - Fraction(1, R * R)),
                            sharp_family_score='64-log2(2-2^-64)',
                            coarse_certified_score_bits=63),
)
(HERE / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
