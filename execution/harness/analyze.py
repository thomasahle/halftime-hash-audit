#!/usr/bin/env python3
"""Turn the harness's JSON result events into epsilon estimates with exact
Poisson (Garwood) 95% intervals and the metric score log2(L/eps)."""
import json, math, sys
from scipy.stats import chi2

def poisson_ci(k, conf=0.95):
    a = 1 - conf
    lo = 0.0 if k == 0 else chi2.ppf(a / 2, 2 * k) / 2
    hi = chi2.ppf(1 - a / 2, 2 * k + 2) / 2
    return lo, hi

def lg(x):
    return math.log2(x) if x > 0 else float('-inf')

def row(d):
    N, k = d["trials"], d["hits"]
    lo, hi = poisson_ci(k)
    eps = k / N
    eps_lo, eps_hi = lo / N, hi / N
    return eps, eps_lo, eps_hi

def main(paths):
    ev = []
    for p in paths:
        for line in open(p):
            line = line.strip()
            if not line.startswith("{"): continue
            d = json.loads(line)
            if d.get("event") == "result": ev.append(d)
    out = []
    for d in ev:
        eps, lo, hi = row(d)
        L = 21 * d["b"]           # message length in 8-byte words for the (A) pairs
        rec = dict(mode=d["mode"], b=d["b"], dispatch=d["dispatch"], sub=d["sub"],
                   pair=d["pair"], len_a=d["len_a"], len_b=d["len_b"],
                   trials=d["trials"], hits=d["hits"], seconds=d["seconds"],
                   seed_hex=d["seed_hex"],
                   eps_point=eps, eps_lo95=lo, eps_hi95=hi,
                   log2_eps_point=lg(eps), log2_eps_lo95=lg(lo), log2_eps_hi95=lg(hi))
        if d["mode"] in ("A", "cond"):
            rec["L_words"] = L
            rec["score_point"] = (lg(L) - lg(eps)) if eps > 0 else None
            rec["score_lower_from_eps_hi"] = lg(L) - lg(hi)   # eps high -> score low
            rec["score_upper_from_eps_lo"] = (lg(L) - lg(lo)) if lo > 0 else None
        out.append(rec)
    json.dump(out, sys.stdout, indent=1)
    print()
    for r in out:
        print("%-9s b=%-2d %-7s %-26s N=2^%.2f hits=%-5d eps=%s  95%%CI=[%s, %s]%s"
              % (r["dispatch"], r["b"], r["sub"], r["pair"], math.log2(r["trials"]), r["hits"],
                 ("2^%.2f" % r["log2_eps_point"]) if r["hits"] else "0",
                 ("2^%.2f" % r["log2_eps_lo95"]) if r["eps_lo95"] > 0 else "0",
                 "2^%.2f" % r["log2_eps_hi95"],
                 ("  score=%.2f (95%% lower %.2f)" % (r["score_point"], r["score_lower_from_eps_hi"]))
                 if r.get("score_point") else ""), file=sys.stderr)

main(sys.argv[1:])
