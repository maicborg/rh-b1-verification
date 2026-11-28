#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "${1:?upstream grh-compact}" && pwd)
TARGET="${2:?target module}"
HERE=$(cd "$(dirname "$0")/.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
cp -R "$HERE/RFH123S" "$WORK/"
mkdir -p "$HERE/logs"
python3 "$HERE/scripts/dependency-map.py" "$HERE" "$TARGET" > "$WORK/order"
cd "$ROOT"
while read -r name deps; do
  echo "=== $name ==="
  lake env bash -c 'export LEAN_PATH="$1:${LEAN_PATH:-}"; lean --tstack=400000 -DmaxHeartbeats=4000000 -DmaxSynthPendingDepth=3 -R "$1" -o "$1/RFH123S/$2.olean" "$1/RFH123S/$2.lean"' _ "$WORK" "$name" 2>&1 | tee "$HERE/logs/$name.log"
  if grep -Eq 'declaration uses .sorry.|sorryAx' "$HERE/logs/$name.log"; then exit 1; fi
done < "$WORK/order"
python3 - "$HERE/logs/$TARGET.log" <<'PY'
import re,sys
from pathlib import Path
lines=re.findall(r"depends on axioms: \[([^\]]*)\]",Path(sys.argv[1]).read_text())
assert lines, "No axiom audit"
allowed={"propext","Classical.choice","Quot.sound"}
for line in lines:
    assert {x.strip() for x in line.split(",") if x.strip()} <= allowed,line
print("AXIOM AUDIT PASS",len(lines))
PY
