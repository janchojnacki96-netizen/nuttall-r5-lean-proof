"""Generate independent Lean replay modules from the exact Fraction witness finder.

The generated Lean checks, not the Python assertions, establish the certificates.
Run from the repository root: python3 tools/r5_compact_replay_modules.py --group 0
Use --all to materialize every module, including the final composition.
"""
import argparse
from pathlib import Path
from r5_compact_replay_bulk import make, lean_cell

PILOTS = {4, 27, 39, 50}
CELLS = [c for c in range(4, 51) if c not in PILOTS]
GROUPS = [CELLS[i:i+8] for i in range(0, len(CELLS), 8)]
assert len(CELLS) == 43 and len(GROUPS) == 6
ROOT = Path(__file__).resolve().parents[1] / "W5"

def write(name, source):
    path = ROOT / (name + ".lean")
    if path.exists() and path.read_text(encoding="utf-8") == source:
        return
    path.write_text(source, encoding="utf-8")

def module(imports, body):
    return "".join("import W5." + name + "\n" for name in imports) + "\nnamespace W5\n\n" + body + "\nend W5\n"

def tag(c):
    return f"{c:02}"

def cert(c):
    return f"thetaOriginalCell{tag(c)}_compactReplay"

def group(g):
    cells = GROUPS[g]
    for c in cells:
        n = tag(c)
        name = "thetaCompactReplayCell" + n
        base = "ThetaCompactReplayBulkData" + n
        arith = "ThetaCompactReplayBulkArith" + n
        gamma = "ThetaCompactReplayBulkGamma" + n
        write(base, module(["ThetaCompactReplayData"], lean_cell(c, make(c))))
        for target, suffix, prop in [(arith, "arithmetic", "ArithmeticFits"), (gamma, "gamma", "GammaFits")]:
            write(target, module([base], f"""set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem {name}_{suffix} :
    ThetaCompactReplay{prop} {name} := by
  native_decide
"""))
        k = c-1
        write("ThetaCompactReplayBulkCert"+n, module(
            ["ThetaRemaining47Reduction", arith, gamma],
            f"""theorem {cert(c)} :
    ThetaUpperRealCellCertificate ((0::endpoints)[{k}]!) (endpoints[{k}]!) := by
  exact thetaCompactReplayCertificate_restrict {name}
    ((0::endpoints)[{k}]!) (endpoints[{k}]!)
    {name}_arithmetic {name}_gamma
    (by native_decide) (by native_decide)
"""))
        print(f"Generated cell {c}", flush=True)
    target = f"ThetaCompactReplayBulkGroup{g}"
    write(target, module(["ThetaCompactReplayBulkCert"+tag(c) for c in cells], ""))
    print("W5."+target, flush=True)

def compose():
    # Explicit indexed endpoints keep the composition independent of the
    # Python witness endpoint representation; Lean checks every equality.
    ends = ", ".join(f"endpoints[{c-1}]!" for c in range(4,51))
    witnesses = ",\n    ".join(cert(c) for c in range(4,51))
    body = f"""set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaRemaining47CompactReplayChain :
    ThetaUpperRealCellCertificateChain (821/2048:ℚ) thetaRemaining47Endpoints := by
  have hs : (821/2048:ℚ) = (0::endpoints)[3]! := by native_decide
  have he : thetaRemaining47Endpoints = [{ends}] := by native_decide
  rw [hs, he]
  exact ⟨{witnesses}, trivial⟩

theorem analyticMatrixPositive_compactReplay : analyticMatrixPositive :=
  analyticMatrixPositive_of_remaining_47_upper_certificates thetaRemaining47CompactReplayChain

#print axioms analyticMatrixPositive_compactReplay
"""
    write("ThetaCompactReplayBulkComplete", module(
        ["ThetaCompactReplayPilotCertificates"] + [f"ThetaCompactReplayBulkGroup{g}" for g in range(len(GROUPS))], body))

if __name__ == "__main__":
    p = argparse.ArgumentParser()
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--group", type=int, choices=range(len(GROUPS)))
    mode.add_argument("--all", action="store_true")
    mode.add_argument("--compose", action="store_true")
    a = p.parse_args()
    if a.all:
        for g in range(len(GROUPS)):
            group(g)
        compose()
    elif a.compose:
        compose()
    else:
        group(a.group)
