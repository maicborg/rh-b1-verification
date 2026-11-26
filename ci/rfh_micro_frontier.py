"""RFH frontier: isolated incremental Lake targets, no terminal build."""
import argparse
import functools
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

p = argparse.ArgumentParser()
p.add_argument("--track", choices=["topg", "vwin"], required=True)
p.add_argument("--manifest", type=Path, required=True)
p.add_argument("--logs", type=Path, required=True)
p.add_argument("--limit", type=int, default=24)
p.add_argument("--seconds", type=int, default=90)
a = p.parse_args()
a.logs.mkdir(parents=True, exist_ok=True)
m = json.loads(a.manifest.read_text())
all_failed = set(m["topg"]) | set(m["vwin"])
roots = ["BuildAid", "CompanionTheory", "Development", "Formalism", "GroundTheory", "Lemmata", "PositivityTheory", "ReciprocityTheory", "Supplements"]
paths = {str(f.with_suffix("")).replace("/", "."): str(f) for root in roots for f in Path(root).rglob("*.lean")}
by_path = {v: k for k, v in paths.items()}
imp = re.compile(r"^\s*(?:(?:public|meta|private)\s+)*import\s+([^\n]+)", re.M)

@functools.lru_cache(None)
def direct(path):
    s = Path(path).read_text(encoding="utf-8")
    # Lean imports are header commands. Exclude commented text, and resolve local names only.
    s = re.sub(r"/-.*?-/", "", s, flags=re.S)
    found = set()
    for line in imp.findall(s):
        for n in line.split("--", 1)[0].split():
            if n in paths:
                found.add(paths[n])
    return frozenset(found)

@functools.lru_cache(None)
def ancestors(path):
    out = set(direct(path))
    for d in direct(path):
        out.update(ancestors(d))
    return frozenset(out)

# The two original producer dependency trees are measured separately.
producer_roots = {
    "topg": ["Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/RFHLiteraturePrelude.lean"],
    "vwin": ["Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean", "Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean"]
}
closure = set(producer_roots[a.track])
for root in producer_roots[a.track]:
    closure.update(ancestors(root))
candidates = list(dict.fromkeys(m["shared"] + m[a.track]))
candidates = [x for x in candidates if x in closure and x in by_path]
rank = {x: i for i, x in enumerate(candidates)}
# Topological ordering by count of known failed ancestors, priority on common roots.
ordered = sorted(candidates, key=lambda x: (len(ancestors(x) & all_failed), rank[x]))
selected = ordered[:a.limit]
plan = {"track": a.track, "closure_local_modules": len(closure), "known_failed_in_closure": len(all_failed & closure), "selected": selected, "remaining": ordered[a.limit:]}
(a.logs / "plan.json").write_text(json.dumps(plan, indent=2))
print("FRONTIER_PLAN", json.dumps(plan), flush=True)
results = {}
for i, path in enumerate(selected, 1):
    name = by_path[path]
    blockers = sorted(d for d in ancestors(path) & set(results) if results[d]["status"] != "green")
    known_unattempted = sorted((ancestors(path) & all_failed) - set(results))
    file = a.logs / f"{i:03d}-{Path(path).stem}.log"
    start = time.monotonic()
    if blockers or known_unattempted:
        status = "blocked"
        file.write_text("Known failed prerequisite(s), not recompiled:\n" + "\n".join(blockers + known_unattempted) + "\n")
    else:
        with file.open("w") as f:
            proc = subprocess.Popen(["lake", "build", name], stdout=f, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = proc.wait(timeout=a.seconds)
                status = "green" if code == 0 else "failure"
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGTERM)
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                status = "timeout"
    results[path] = {"status": status, "seconds": round(time.monotonic()-start, 1), "module": name, "log": file.name}
    (a.logs / "results.json").write_text(json.dumps(results, indent=2))
    print("MICRO", i, status, name, results[path]["seconds"], flush=True)
    if status != "green":
        print("\n".join(file.read_text(errors="replace").splitlines()[-8:]), flush=True)

print("MICRO_SUMMARY", json.dumps({s: sum(x["status"] == s for x in results.values()) for s in ["green", "failure", "timeout", "blocked"]}), flush=True)
# A blocked target is not green. Partial artifacts are retained by the workflow.
raise SystemExit(0 if len(results) == a.limit and all(x["status"] == "green" for x in results.values()) else 1)
