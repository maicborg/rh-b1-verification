#!/usr/bin/env python3
"""Compute local import closure; report omitted tests without deleting them."""
from pathlib import Path
import json
import re
import sys

root = Path(sys.argv[1])
target = sys.argv[2]
files = {p.stem: p for p in (root / "RFH123S").glob("*.lean")}
graph = {}
external = {}
for name, path in files.items():
    text = path.read_text()
    imports = []
    for line in text.splitlines():
        m = re.match(r"^\s*(?:(?:public|private|meta)\s+)?import\s+([^/]+)", line)
        if m:
            imports.extend(m.group(1).split())
    graph[name] = [x.removeprefix("RFH123S.") for x in imports if x.startswith("RFH123S.")]
    external[name] = [x for x in imports if not x.startswith("RFH123S.")]
order, active, seen = [], set(), set()
def visit(name):
    if name in active:
        raise ValueError(f"Import cycle: {name}")
    if name in seen:
        return
    if name not in files:
        raise ValueError(f"Missing local dependency: {name}")
    if "New.Main" in external[name]:
        raise ValueError(f"Forbidden direct terminal import: {name}")
    active.add(name)
    for dep in graph[name]:
        visit(dep)
    active.remove(name)
    seen.add(name)
    order.append(name)
visit(target)
if "Baseline" in seen:
    raise ValueError("Baseline in final dependency closure")
excluded = sorted(set(files) - seen)
report = {"target": target, "required_count": len(order), "total_local_modules": len(files),
          "required_order": order, "excluded": excluded,
          "local_edges": {name: graph[name] for name in order},
          "direct_external_imports": sorted({x for name in order for x in external[name]})}
(root / "logs").mkdir(exist_ok=True)
(root / "logs" / "dependency-map.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2), file=sys.stderr)
for name in order:
    print(name, *graph[name])
