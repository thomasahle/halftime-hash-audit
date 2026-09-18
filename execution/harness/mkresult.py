#!/usr/bin/env python3
"""Assemble result.json from the harness logs."""
import json, math, sys, hashlib, os
from scipy.stats import chi2

def poisson_ci(k, conf=0.95):
    a = 1 - conf
    lo = 0.0 if k == 0 else chi2.ppf(a / 2, 2 * k) / 2
    hi = chi2.ppf(1 - a / 2, 2 * k + 2) / 2
    return lo, hi

def lg(x): return math.log2(x) if x > 0 else None

def load(paths):
    out = []
    for p in paths:
        if not os.path.exists(p): continue
        for line in open(p):
            line = line.strip()
            if not line.startswith("{"): continue
            d = json.loads(line)
            if d.get("event") == "result":
                d["_log"] = os.path.basename(p)
                out.append(d)
    return out

def enrich(d):
    N, k = d["trials"], d["hits"]
    lo, hi = poisson_ci(k)
    r = dict(source_log=d["_log"], mode=d["mode"], sub=d["sub"], b=d["b"],
             dispatch=d["dispatch"], pair=d["pair"],
             len_a_bytes=d["len_a"], len_b_bytes=d["len_b"],
             trials=N, log2_trials=round(math.log2(N), 4), hits=k,
             seconds=d["seconds"], seed_hex=d["seed_hex"],
             high32_key6_zero=d["high32_key6_zero"],
             miss_when_high32_key6_zero=d["miss_when_zero"],
             hit_when_high32_key6_nonzero=d["hit_when_nonzero"],
             variant2_collision_equals_high32_zero_count=d["variant2_agrees_with_high32"],
             eps_point=k / N, eps_lo95=lo / N, eps_hi95=hi / N,
             log2_eps_point=lg(k / N), log2_eps_lo95=lg(lo / N), log2_eps_hi95=lg(hi / N))
    if d["mode"] in ("A", "cond"):
        L = 21 * d["b"]
        r["L_words"] = L
        r["score_point_log2_L_over_eps"] = (math.log2(L) - lg(k / N)) if k else None
        r["score_conservative_from_eps_hi95"] = math.log2(L) - lg(hi / N)
        r["score_from_eps_lo95"] = (math.log2(L) - lg(lo / N)) if k else None
    return r

logs = sys.argv[1:]
rows = [enrich(d) for d in load(logs)]
json.dump(rows, sys.stdout, indent=1)
