"""Generate rank-eight replay modules that reuse the split Ψ₁ cell data."""

import argparse
import json
from pathlib import Path


def modules(i, anchor, cell):
    hi = i + 1
    basis = ",\n".join("  #v[" + ", ".join(map(str, row)) + "]"
                        for row in cell["basis"])
    lo = cell["corner"][0]
    return f"""import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell{i}Data

namespace Nuttall

open W5

def psiTwoCell{i}Corner : FixedIntInterval := ⟨{lo}, {cell["corner"][1]}⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
{basis}
]

def psiTwoCell{i}Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell{i}Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell{i}Basis psiOneCell{i}Snapshot.corner psiTwoCell{i}Corner
      psiOneCell{i}Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell{i}Margin_checked

end Nuttall
""", f"""import Nuttall.PsiTwoCompactCell{i}Margin
import Nuttall.PsiCompactCell{i}Jets
import Nuttall.PsiTwoCompactAnchor{anchor}

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell{i}Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := {anchor}/32 - psiOneDyadicCenter {i}
    let rawOne := psiOnePanelBox psiOneCompactAnchor{anchor} jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor{anchor} psiTwoCompactAnchor{anchor} jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell{i}Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell{i}Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell{i}_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : {i}/128 ≤ t) (hU : t ≤ {hi}/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound {i} {anchor} (by decide) (by decide +kernel)
    psiOneCompactAnchor{anchor} psiTwoCompactAnchor{anchor} ?_ ?_ psiOneCell{i}Snapshot psiTwoCell{i}Corner
    psiOneCell{i}Inputs_checked psiOneCell{i}Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell{i}Basis ?_ ?_ ?_ psiTwoCell{i}Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor{anchor}_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor{anchor}_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change ({i}:ℝ)/128 ≤ t
    exact hL
  · change t ≤ ({hi}:ℝ)/128
    exact hU

#print axioms psiTwo_compact_cell{i}_signed_wronskians

end Nuttall
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("psi_one_certificate", type=Path)
    parser.add_argument("psi_two_certificate", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("indices", nargs="+", type=int)
    args = parser.parse_args()
    one = json.loads(args.psi_one_certificate.read_text())
    two = json.loads(args.psi_two_certificate.read_text())
    assert one["scale"] == two["scale"] == 2**90
    assert two["basis_scale"] == 1024
    pending = {}
    for i in args.indices:
        if i < 0 or i > 47:
            parser.error("choose a cell in the uniform range from 0 to 47")
        left, right = one["cells"][i], two["cells"][i]
        assert left["index"] == right["index"] == i
        assert all(row[j] and not any(row[j+1:]) for j, row in enumerate(right["basis"]))
        margin, proof = modules(i, left["anchor_index"], right)
        pending[f"PsiTwoCompactCell{i}Margin.lean"] = margin
        pending[f"PsiTwoCompactCell{i}.lean"] = proof

    for name in pending:
        if (args.output_dir / name).exists():
            parser.error(f"refusing to overwrite {name}")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, contents in pending.items():
        (args.output_dir / name).write_text(contents)


if __name__ == "__main__":
    main()
