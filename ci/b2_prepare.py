#!/usr/bin/env python3
"""B2 compatibility patches. Preflight runs against pinned source BEFORE any Lean build.

Usage:
  python3 ci/b2_prepare.py --root alpoge/src --bridge bridge --mode check
  python3 bridge/ci/b2_prepare.py --root upstream/lean --bridge bridge --mode apply

Only checked-out copies of Alpoge may be modified; the original repos are untouched.
"""
from __future__ import annotations
import argparse
import difflib
import json
import re
from pathlib import Path

J = "Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/"
FIXES = {
    J + "ExistsFarFromPoints.lean": [("Finset.prod_le_prod", "Finset.prod_le_prod₀", 1)],
    "Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LandauLocalOf.lean":
        [("Finset.prod_le_prod", "Finset.prod_le_prod₀", 2)],
    "Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SameCharacterLFunctionOne.lean":
        [("Finset.prod_le_prod", "Finset.prod_le_prod₀", 2),
         ("Finset.prod_le_one", "Finset.prod_le_one₀", 1)],
    J + "Turan2Main.lean": [("Finset.prod_le_prod", "Finset.prod_le_prod₀", 1)],
    "Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExistsLocalZeroExpansionOfBound.lean":
        [("Finset.prod_le_prod", "Finset.prod_le_prod₀", 2)],
    "Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/EulerFactorLogDerivBound.lean":
        [("logDeriv_prod (f :=", "logDeriv_fun_prod (f :=", 1)],
    J + "PNTDHLocalA.lean": [("Finset.prod_le_prod", "Finset.prod_le_prod₀", 1)],
    J + "PNTExplLF.lean": [("Finset.prod_le_prod", "Finset.prod_le_prod₀", 1)],
    J + "PNTExplLoc.lean": [("Finset.prod_le_prod", "Finset.prod_le_prod₀", 2)],
    "Formalism/LFunctionBounds/LFunctionBoundsProofs/DivisorBound.lean":
        [("Finset.prod_le_prod", "Finset.prod_le_prod₀", 1)],
}
DYADIC = [
    J + "SecondBlockCount.lean",
    J + "ZeroCountFirst.lean",
]
COPRIME = J + "MSqTwistB.lean"
MEAN = "Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean"
STAGE = "Development/AutomorphicArithmetic/MeanSquareBounds/StagePow.lean"
BRIDGES = [
    "B2NoExceptional", "B2JacobiClassZero", "B2IntegratedBridge",
    "B2JacobiRelativeActual", "B2PrimeSetOneEndpoint",
    "B2SmallErrorBudget", "B2CountRelativeActualV3",
    "B2AdmittedLogModulusV3", "B2PNTThresholdFromBudget",
    "B2UniformPNTFromAdmittedV4", "B2JacobiEnvelopeV3",
    "B2ExponentFromAdmittedV4", "B2LowEndpointDecayV2",
    "B2TwistKNoExceptionConditionalV5", "B2RealPNT",
]

def one(text: str, before: str, after: str, n: int, path: str) -> str:
    actual = text.count(before)
    if actual != n:
        raise ValueError(f"{path}: expected {n} occurrences of {before!r}, found {actual}")
    return text.replace(before, after)

def prepare(root: Path, bridge: Path, mode: str) -> None:
    for name in BRIDGES:
        if not (bridge / (name + ".lean")).is_file():
            raise ValueError(f"Missing bridge source: {name}.lean")

    changed = {}
    for rel, edits in FIXES.items():
        path = root / rel
        text = path.read_text(encoding="utf-8")
        new = text
        for old, replacement, count in edits:
            new = one(new, old, replacement, count, rel)
        changed[rel] = (text, new)

    # The original Lean source has variable indentation; matching 12/13 spaces
    # literally caused the previous run to fail BEFORE Lean was ever started.
    dyadic_regex = re.compile(
        r"(?m)^([ \t]*)gcongr[ \t]*\n[ \t]*· norm_num[ \t]*\n[ \t]*· omega[ \t]*$"
    )
    for rel in DYADIC:
        path = root / rel
        text = path.read_text(encoding="utf-8")
        new, count = dyadic_regex.subn(
            lambda m: m.group(1) + "gcongr <;> omega", text
        )
        if count != 1:
            raise ValueError(f"{rel}: expected 1 dyadic gcongr block, found {count}")
        changed[rel] = (text, new)

    text = (root / COPRIME).read_text(encoding="utf-8")
    new = one(text, "exact Nat.Coprime.mul hb.2.2 hus",
              "exact Nat.Coprime.mul_left hb.2.2 hus", 1, COPRIME)
    new = one(new, "Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right",
              "Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_right", 1, COPRIME)
    changed[COPRIME] = (text, new)

    text = (root / MEAN).read_text(encoding="utf-8")
    new = one(text, "import Development.AutomorphicArithmetic.MeanSquareBounds.twistK",
              "import Development.AutomorphicArithmetic.MeanSquareBounds.B2TwistKNoExceptionConditionalV5\n"
              "import Development.AutomorphicArithmetic.MeanSquareBounds.B2RealPNT", 1, MEAN)
    new = one(new, ":= twistK ε (800 * K) (K + 1)",
              ":= b2_twistK_no_exception_of_seven_eighths_v5 "
              "BorghettiRH.b2_actual_h78 ε (800 * K) (K + 1)", 1, MEAN)
    changed[MEAN] = (text, new + "\n#print axioms QH.meanSqK\n")

    text = (root / STAGE).read_text(encoding="utf-8")
    changed[STAGE] = (text, text + "\n#print axioms QH.stage\n")

    summary = []
    for rel, (before, after) in changed.items():
        if before == after:
            raise ValueError(f"{rel}: patch had no effect")
        if mode == "apply":
            (root / rel).write_text(after, encoding="utf-8")
        diff = list(difflib.unified_diff(before.splitlines(), after.splitlines(),
                                         fromfile=rel + " original",
                                         tofile=rel + " adapted", lineterm=""))
        summary.append({"file": rel, "changed_lines": len(diff)})
        print("\n".join(diff[:60]))
    print("B2_PREFLIGHT_OK " + json.dumps({"mode": mode, "files": summary,
                                           "bridge_files": len(BRIDGES)}))

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--bridge", type=Path, required=True)
    parser.add_argument("--mode", choices=("check", "apply"), required=True)
    args = parser.parse_args()
    prepare(args.root, args.bridge, args.mode)
