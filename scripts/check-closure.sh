#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "${1:?upstream grh-compact}" && pwd)
HERE=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
cp -R "$HERE/RFH123S" "$WORK/"
mkdir -p "$HERE/logs"
python3 "$HERE/scripts/dependency-map.py" "$HERE" DependencyAudit > "$WORK/order"
status=0
declare -A done
while read -r name deps; do
  blocked=0
  for dep in $deps; do
    if [[ "${done[$dep]:-0}" != 1 ]]; then
      echo "BLOCKED $name by $dep" | tee "$HERE/logs/$name.log"
      status=1
      blocked=1
      break
    fi
  done
  if [[ "$blocked" == 1 ]]; then continue; fi
  echo "=== $name ==="
  if lake env bash -c 'export LEAN_PATH="$1:${LEAN_PATH:-}"; lean --tstack=400000 -DmaxHeartbeats=4000000 -DmaxSynthPendingDepth=3 -R "$1" -o "$1/RFH123S/$2.olean" "$1/RFH123S/$2.lean"' _ "$WORK" "$name" 2>&1 | tee "$HERE/logs/$name.log"; then
    if grep -Eq 'declaration uses .sorry.|sorryAx' "$HERE/logs/$name.log"; then
      echo "FAIL $name: sorry detected"
      status=1
    else
      done[$name]=1
      echo "PASS $name"
    fi
  else
    echo "FAIL $name"
    status=1
  fi
done < "$WORK/order"
if [[ "${done[DependencyAudit]:-0}" != 1 ]]; then
  exit 1
fi
# Audit every reported axiom list, not merely the absence of sorryAx.
python3 - "$HERE/logs/DependencyAudit.log" <<'PY'
import re, sys
from pathlib import Path
s = Path(sys.argv[1]).read_text()
lists = re.findall(r"depends on axioms: \[([^\]]*)\]", s)
assert len(lists) == 5, f"Expected five axiom audits, got {len(lists)}"
allowed = {"propext", "Classical.choice", "Quot.sound"}
for xs in lists:
    assert set(x.strip() for x in xs.split(",") if x.strip()) <= allowed, xs
assert "Terminal import exclusion: PASS" in s
print("Dependency and axiom audit: PASS")
PY
exit "$status"
