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


def jet_module(i):
    return f"""import Nuttall.PsiCompactCell{i}Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell{i}Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter {i}) ∧
      psiPreciseGridInputs (psiOneDyadicCenter {i}) = psiOneCell{i}Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell{i}Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell{i}Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell{i}Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
"""


def cell_module(i, anchor):
    anchor_name = f"psiOneCompactAnchor{anchor}"
    return f"""import Nuttall.PsiCompactCell{i}Margin
import Nuttall.PsiCompactCell{i}Jets
import Nuttall.PsiCompactUniformPanel{anchor}

namespace Nuttall

open W5

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
    {anchor_name} ?_ psiOneCell{i}Snapshot psiOneCell{i}Inputs_checked psiOneCell{i}Jets_checked
    corner_checked psiOneCell{i}Margin_checked p hp t ?_ ?_
  · have hanchor : (({anchor}/32:ℚ):ℝ) = ((({anchor}:ℕ):ℝ)/32) := by norm_num
    rw [← hanchor]
    exact {anchor_name}_containsReal
  · change ((({i}:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ ((({i + 1}:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiOne_compact_cell{i}_signed_wronskians

end Nuttall
"""


def uniform_panel_modules(i, node, panel):
    next_i = i + 1
    inputs = ",\n  ".join(f"bounds ({lo}) ({hi})" for lo, hi in node["inputs"])
    jets = ",\n".join(f"  ({lo}, {hi})" for lo, hi in node["jets"])
    lo, hi = panel
    return f"""import Nuttall.PsiCompactPanelStep

namespace Nuttall

open W5

private def bounds (lo hi : ℤ) : QInterval :=
  ⟨(lo:ℚ)/2^90, (hi:ℚ)/2^90⟩

private def gridInputs : PsiPreciseGridInputs :=
  ⟨{inputs}⟩

private def endpoints : Vector (ℤ × ℤ) 36 := #v[
{jets}
]

def psiOneUniformPanel{i}Jet (j : ℕ) : QInterval :=
  let e := endpoints.toArray[j]!
  bounds e.1 e.2

def psiOneUniformPanel{i} : QInterval :=
  bounds {lo} {hi}

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem inputCheck :
    psiPreciseGridChecks ({i}/32) ∧ psiPreciseGridInputs ({i}/32) = gridInputs := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem jetCheck (j : ℕ) (hj : j < 36) :
    psiOneUniformPanel{i}Jet j = psiFixedGridPhiJetBoxOfInputs gridInputs j := by
  interval_cases j <;> decide +kernel

theorem psiOneUniformPanel{i}Jet_containsReal (j : ℕ) (hj : j < 36) :
    (psiOneUniformPanel{i}Jet j).ContainsReal (iteratedDeriv j Phi (({i}/32:ℚ):ℝ)) := by
  rw [jetCheck j hj]
  exact psiFixedGridPhiJetBoxOfInputs_containsReal (by norm_num) (by norm_num)
    inputCheck.1 inputCheck.2 j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneUniformPanel{i}_checked :
    let raw := psiOnePanelBox (QInterval.point 0) psiOneUniformPanel{i}Jet 36 (1/32)
    psiOneUniformPanel{i}.lo ≤ raw.lo ∧ raw.hi ≤ psiOneUniformPanel{i}.hi := by
  decide +kernel

#print axioms psiOneUniformPanel{i}Jet_containsReal
#print axioms psiOneUniformPanel{i}_checked

end Nuttall
""", f"""import Nuttall.PsiCompactUniformPanel{i}Data
import Nuttall.PsiCompactUniformPanel{next_i}

namespace Nuttall

open W5

def psiOneCompactAnchor{i} : QInterval := psiOneCompactAnchor{next_i}.add psiOneUniformPanel{i}

theorem psiOneCompactAnchor{i}_containsReal : psiOneCompactAnchor{i}.ContainsReal (psi 1 (({i}/32:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor{next_i}.ContainsReal (psi 1 ((({i}+1:ℕ):ℝ)/32)) := by
    simpa [show ((({i}+1:ℕ):ℝ)/32) = (({next_i}/32:ℚ):ℝ) by norm_num] using
      psiOneCompactAnchor{next_i}_containsReal
  have hnode : (({i}/32:ℚ):ℝ) = ((({i}:ℕ):ℝ)/32) := by norm_num
  have hj (j : ℕ) (hj : j < 36) :
      (psiOneUniformPanel{i}Jet j).ContainsReal (iteratedDeriv j Phi ((({i}:ℕ):ℝ)/32)) := by
    rw [← hnode]
    exact psiOneUniformPanel{i}Jet_containsReal j hj
  rw [hnode]
  exact psiOne_compact_panel_step (i := {i}) (by decide) hright hj psiOneUniformPanel{i}_checked

#print axioms psiOneCompactAnchor{i}_containsReal

end Nuttall
"""



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("indices", nargs="+", type=int)
    parser.add_argument("--uniform-panels", action="store_true")
    args = parser.parse_args()
    data = json.loads(args.certificate.read_text())
    assert data["scale"] == 2**90
    pending = {}
    for i in args.indices:
        if args.uniform_panels:
            if i < 1 or i > 11:
                parser.error("choose uniform panels from 1 to 11")
            node = data["nodes"][i]
            assert Fraction(node["t"]) == Fraction(i, 32)
            module_data, anchor_code = uniform_panel_modules(i, node, data["uniform_panels"][i])
            pending[f"PsiCompactUniformPanel{i}Data.lean"] = module_data
            pending[f"PsiCompactUniformPanel{i}.lean"] = anchor_code
            continue
        if i < 0 or i > 51:
            parser.error("choose uniform cells from 0 to 51")
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
        pending[stem + "Jets.lean"] = jet_module(i)
        # The origin already has a rank-seven proof. Emit only the snapshot
        # and its jet checks there so the rank-eight replay can reuse them.
        if i != 0:
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
