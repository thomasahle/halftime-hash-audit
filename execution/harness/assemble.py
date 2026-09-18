#!/usr/bin/env python3
"""Aggregate the harness logs into the (A) results table and result.json."""
import json, math, collections, sys, os
from scipy.stats import chi2

LOGS = ["verify2/logs/phase1.jsonl", "verify2/logs/sweep.jsonl",
        "verify2/logs/sweep3.jsonl", "verify2/logs/cond.jsonl", "verify2/logs/sweep4.jsonl", "verify2/logs/sweep5.jsonl", "verify2/logs/sweep6.jsonl"]

def ci(k):
    lo = 0.0 if k == 0 else chi2.ppf(0.025, 2 * k) / 2
    hi = chi2.ppf(0.975, 2 * k + 2) / 2
    return lo, hi

def load():
    out = []
    for p in LOGS:
        if not os.path.exists(p): continue
        for l in open(p):
            l = l.strip()
            if '"event":"result"' not in l: continue
            d = json.loads(l); d["_log"] = os.path.basename(p); out.append(d)
    return out

rows = load()

# ---- aggregate mode A by (dispatch-family, b, pair)
def family(disp): return "scalar" if disp.endswith("Scalar") else "native"
agg = collections.defaultdict(lambda: {"trials": 0, "hits": 0, "seconds": 0.0,
                                       "runs": 0, "hit_when_nonzero": 0,
                                       "miss_when_zero": 0, "seeds": [], "dispatch": "",
                                       "len": 0})
for d in rows:
    if d["mode"] != "A": continue
    k = (family(d["dispatch"]), d["b"], d["pair"])
    a = agg[k]
    a["trials"] += d["trials"]; a["hits"] += d["hits"]; a["seconds"] += d["seconds"]
    a["runs"] += 1; a["hit_when_nonzero"] += d["hit_when_nonzero"]
    a["miss_when_zero"] += d["miss_when_zero"]; a["dispatch"] = d["dispatch"]
    a["len"] = d["len_a"]
    if d["seed_hex"] not in a["seeds"]: a["seeds"].append(d["seed_hex"])

def fmt2(x): return ("2^%.2f" % math.log2(x)) if x > 0 else "0"

def table(fam):
    lines = []
    for b in (1, 2, 4, 8):
        for pair in ("word_6b", "word_6b_plus_1"):
            k = (fam, b, pair)
            if k not in agg: continue
            a = agg[k]; N, h = a["trials"], a["hits"]
            lo, hi = ci(h); L = 21 * b
            score = math.log2(L) - math.log2(h / N) if h else float("nan")
            lines.append("| %d | `%s` | %s | %d (2^%.2f) | **%d** | %s | [%s, %s] | %.2f |"
                         % (b, a["dispatch"], pair.replace("_", " "), N, math.log2(N), h,
                            fmt2(h / N), fmt2(lo / N), fmt2(hi / N), score))
    return "\n".join(lines)

hdr = ("| b | dispatch | pair | trials | hits | eps | exact Poisson 95% CI | "
       "score `log2(21b/eps)` |\n|---:|---|---|---:|---:|---|---|---:|")
print("#SCALAR#"); print(hdr); print(table("scalar"))
print("#NATIVE#"); print(hdr); print(table("native"))

# ---- result.json
def enrich(d):
    N, k = d["trials"], d["hits"]
    lo, hi = ci(k)
    r = dict(source_log=d["_log"], mode=d["mode"], sub=d["sub"], b=d["b"],
             dispatch=d["dispatch"], pair=d["pair"], len_a_bytes=d["len_a"],
             len_b_bytes=d["len_b"], trials=N, log2_trials=round(math.log2(N), 4),
             hits=k, seconds=d["seconds"], seed_hex=d["seed_hex"],
             high32_key6_zero=d["high32_key6_zero"],
             miss_when_high32_key6_zero=d["miss_when_zero"],
             hit_when_high32_key6_nonzero=d["hit_when_nonzero"],
             eps_point=k / N, eps_lo95=lo / N, eps_hi95=hi / N)
    if d["mode"] in ("A", "cond"):
        L = 21 * d["b"]; r["L_words"] = L
        r["score_point_log2_L_over_eps"] = (math.log2(L) - math.log2(k / N)) if k else None
        r["score_conservative_from_eps_hi95"] = math.log2(L) - math.log2(hi / N)
    return r

aggregates = []
for (fam, b, pair), a in sorted(agg.items()):
    N, h = a["trials"], a["hits"]; lo, hi = ci(h); L = 21 * b
    aggregates.append(dict(dispatch_family=fam, dispatch=a["dispatch"], b=b, pair=pair,
                           message_bytes=a["len"], runs_combined=a["runs"],
                           trials=N, log2_trials=round(math.log2(N), 4), hits=h,
                           cpu_wall_seconds=a["seconds"], seeds=a["seeds"],
                           hits_when_high32_key6_nonzero=a["hit_when_nonzero"],
                           misses_when_high32_key6_zero=a["miss_when_zero"],
                           eps_point=h / N, eps_lo95=lo / N, eps_hi95=hi / N,
                           log2_eps_point=math.log2(h / N) if h else None,
                           L_words=L,
                           score_point=math.log2(L) - math.log2(h / N) if h else None,
                           score_conservative_from_eps_hi95=math.log2(L) - math.log2(hi / N)))

json.dump({"per_run": [enrich(d) for d in rows], "aggregated_A": aggregates},
          open("result.json", "w"), indent=1)
sys.stderr.write("wrote result.json with %d per-run rows and %d aggregates\n"
                 % (len(rows), len(aggregates)))
