"""Emit Lean replay modules for selected cells of the exact Ψ₁ certificate.

The input is produced by preprint_psi_one_compact_probe.py --output.
The output directory is explicit so generated files can be reviewed before
adding them to Nuttall. Existing module files are preserved.
"""

import argparse
import json
from fractions import Fraction
from pathlib import Path


def data_module(i, node, corner):
    inputs = ",\n  ".join(f"bounds ({lo}) ({hi})" for lo, hi in node["inputs"])
    jets = ",\n".join(f"  ({lo}, {hi})" for lo, hi in node["jets"])
    return f"""import Nuttall.PsiOneCompactDyadicReplay

namespace Nuttall

open W5

private def bounds (lo hi : ℤ) : QInterval :=
  (⟨lo, hi⟩ : FixedIntInterval).asQInterval (2^90)

private def inputs : PsiPreciseGridInputs :=
  ⟨{inputs}⟩

private def endpoints : Vector (ℤ × ℤ) 36 := #v[
{jets}
]

def psiOneCell{i}Snapshot : PsiOneDyadicSnapshot :=
  ⟨inputs, (fun j =>
    let p := endpoints.toArray[j]!
    ⟨p.1, p.2⟩), ⟨{corner[0]}, {corner[1]}⟩⟩

end Nuttall
"""


def margin_module(i):
    return f"""import Nuttall.PsiCompactCell{i}Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell{i}Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow {i} psiOneCell{i}Snapshot.corner psiOneCell{i}Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell{i}Margin_checked

end Nuttall
"""


def cell_module(i, anchor):
    anchor_name = f"psiOneCompactAnchor{anchor}"
    return f"""import Nuttall.PsiCompactCell{i}Margin
import Nuttall.PsiCompactUniformPanel{anchor}

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem input_checked :
    psiPreciseGridChecks (psiOneDyadicCenter {i}) ∧
      psiPreciseGridInputs (psiOneDyadicCenter {i}) = psiOneCell{i}Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell{i}Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell{i}Snapshot.input j := by
  interval_cases j <;> decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox {anchor_name}
      (fun j => (psiOneCell{i}Snapshot.jets j).asQInterval (2^90)) 36
      ({anchor}/32 - psiOneDyadicCenter {i})
    (psiOneCell{i}Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell{i}Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell{i}_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : {i}/128 ≤ t) (hU : t ≤ {i + 1}/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound {i} {anchor} (by decide) (by decide +kernel)
    {anchor_name} ?_ psiOneCell{i}Snapshot input_checked jets_checked
    corner_checked psiOneCell{i}Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      {anchor_name}_containsReal
  · change ({i}:ℝ)/128 ≤ t
    exact hL
  · change t ≤ ({i + 1}:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell{i}_signed_wronskians

end Nuttall
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("indices", nargs="+", type=int)
    args = parser.parse_args()
    data = json.loads(args.certificate.read_text())
    assert data["scale"] == 2**90
    pending = {}
    for i in args.indices:
        if i < 1 or i > 51:
            parser.error("choose uniform cells from 1 to 51")
        cell = data["cells"][i]
        node = cell["center"]
        anchor = cell["anchor_index"]
        assert cell["index"] == i and len(node["inputs"]) == 3 and len(node["jets"]) == 36
        assert Fraction(node["t"]) == Fraction(2*i+1, 256)
        assert Fraction(node["t"]) + Fraction(cell["width"]) == Fraction(anchor, 32)
        assert Fraction(cell["left"]) == Fraction(i, 128)
        assert Fraction(cell["right"]) == Fraction(i+1, 128)
        assert max(cell["row_numerators"]) < 7 * data["scale"] // 10
        stem = f"PsiCompactCell{i}"
        pending[stem + "Data.lean"] = data_module(i, node, cell["corner"])
        pending[stem + "Margin.lean"] = margin_module(i)
        pending[stem + ".lean"] = cell_module(i, anchor)
    for name in pending:
        if (args.output_dir / name).exists():
            parser.error(f"refusing to overwrite {name}")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, contents in pending.items():
        (args.output_dir / name).write_text(contents)


if __name__ == "__main__":
    main()
