#!/usr/bin/env python3
"""Turn the audited 51×15 scaled-integer JSON export into Lean 4 data definitions.

This converter DOES NOT prove the 15×51 theta analytic enclosures.
It only gives exact, losslessly encoded, rational interval constants that
can be checked by the already proved finite LDL checker in Lean.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path


def lean_q(value: str) -> str:
    q = Fraction(value)
    return f"(({q.numerator} : ℚ) / ({q.denominator} : ℚ))"


def interval_literal(lo: str, hi: str) -> str:
    a, b = int(lo), int(hi)
    assert a <= b
    return (f"(⟨(({a} : ℤ) : ℚ) / thetaAuditScaleQ, "
            f"(({b} : ℤ) : ℚ) / thetaAuditScaleQ⟩ : QInterval)")


def write_lean(data: dict) -> str:
    assert data["scale_power_of_two"] == 768
    cells = data["cells"]
    assert len(cells) == 51
    lines = [
        "import W5.ThetaSymmetric15EntryCellCertificates",
        "",
        "/-!",
        "# Exact 768-bit candidate theta interval matrices from the integer audit",
        "",
        "These are DATA only, not a proof of the analytic theta enclosures.",
        "Each full 5×5 matrix is reconstructed from 15 integer interval",
        "entries by the previously proved symmetric completion.",
        "The strict pivot checks should be proved separately using the",
        "finite Boolean LDL checker. The input JSON came from the independent",
        "arbitrary-precision Python audit, not from an assumed Lean theorem.",
        "-/",
        "",
        "namespace W5",
        "",
        "def thetaAuditScaleQ : ℚ := (2 : ℚ) ^ 768",
        "",
    ]
    names = []
    endpoints = []
    previous = None
    for idx, cell in enumerate(cells, start=1):
        assert cell["cell"] == idx
        left, right = Fraction(cell["left"]), Fraction(cell["right"])
        assert left <= right
        if previous is not None:
            assert previous == left
        previous = right
        upper = cell["upper"]
        assert len(upper) == 15
        name = f"thetaAuditUpperCell_{idx:02d}"
        full = f"thetaAuditCell_{idx:02d}"
        lines.extend([
            f"/-- Raw 768-bit audit matrix for cell {idx}, x ∈ [{left},{right}]. -/",
            f"def {name} : Matrix (Fin 5) (Fin 5) QInterval :=",
            "  Matrix.of (fun i j =>",
        ])
        pos = 0
        for i in range(5):
            for j in range(i, 5):
                lo, hi = upper[pos]
                pos += 1
                prefix = "    if" if pos == 1 else "    else if"
                lines.extend([
                    f"{prefix} i.val = {i} ∧ j.val = {j} then",
                    "      " + interval_literal(lo, hi),
                ])
        lines.extend([
            "    else (⟨0, 0⟩ : QInterval))",
            "",
            f"def {full} : Matrix (Fin 5) (Fin 5) QInterval :=",
            f"  thetaSymmetricIntervals {name}",
            "",
        ])
        names.append(full)
        endpoints.append(f"  ({lean_q(str(left))}, {lean_q(str(right))})")

    assert Fraction(cells[0]["left"]) == 0
    assert Fraction(cells[-1]["right"]) == Fraction(145, 256)
    lines.extend([
        "/-- All 51 original checker matrices in increasing x order. -/",
        "def thetaAuditCellMatrices :",
        "    List (Matrix (Fin 5) (Fin 5) QInterval) := [",
        "  " + ",\n  ".join(names),
        "]",
        "",
        "/-- Rational bounds of the same 51 cells; coverage was already",
        "proved separately in W5.FiniteCore. -/",
        "def thetaAuditCellBounds : List (ℚ × ℚ) := [",
        ",\n".join(endpoints),
        "]",
        "",
        "theorem thetaAuditCellMatrices_length :",
        "    thetaAuditCellMatrices.length = 51 := by decide",
        "",
        "theorem thetaAuditCellBounds_length :",
        "    thetaAuditCellBounds.length = 51 := by decide",
        "",
        "end W5",
        "",
    ])
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input_json", type=Path)
    parser.add_argument("output_lean", type=Path)
    args = parser.parse_args()
    data = json.loads(args.input_json.read_text(encoding="utf-8"))
    output = write_lean(data)
    args.output_lean.parent.mkdir(parents=True, exist_ok=True)
    args.output_lean.write_text(output, encoding="utf-8")
    print(f"EXPORTED 51 exact Lean 4 candidate interval matrices to {args.output_lean}")


if __name__ == "__main__":
    main()
