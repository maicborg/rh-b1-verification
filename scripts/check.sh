#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "${1:?upstream grh-compact}" && pwd)
HERE=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
cp -R "$HERE/RFH123S" "$WORK/"
mkdir -p "$HERE/logs"
status=0
declare -A done
run() {
  local name=$1
  shift
  local dep
  for dep in "$@"; do
    if [[ "${done[$dep]:-0}" != 1 ]]; then
      echo "BLOCKED $name by $dep" | tee "$HERE/logs/$name.log"
      status=1
      return 0
    fi
  done
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
}
run Period
run Scale
run GeometryAudit
run Star
run Point Star
run Producers Point Scale
run Final Producers
run Baseline Star
run LiftRefined
run VolumeRefined LiftRefined
run CostLocal Point
run CostAsymptotic
run CostBridge Producers CostLocal CostAsymptotic
run TailScalar CostAsymptotic
run TailBridge Producers TailScalar
run ScaleEventually Scale CostAsymptotic
run ThickOrder
run ThickCongruence ThickOrder
run ReducedFinal Final CostBridge TailBridge
run DensityAlgebra
run RankScale
run DensityBase
run DensityBudget
run PrimePair
run PrimeWindows PrimePair
exit "$status"
