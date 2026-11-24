#!/usr/bin/env python3
"""Independent exact-rational replay of the exported 768-bit W5 LDL matrix.

Uses fractions.Fraction for ALL calculations. This is not a rewrite of
the fixed-point evaluator: it starts with its exported INITIAL matrices,
performs all Schur updates in exact rational interval arithmetic
(without any rounding), and independently checks all 255 pivot signs.

Does NOT independently prove the 15 theta coefficient enclosures.
Lean verification of their transcendental bounds remains outstanding.
"""
from __future__ import annotations
from fractions import Fraction
from pathlib import Path
import argparse
import json


def sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def mul(a, b):
    products = [x * y for x in a for y in b]
    return min(products), max(products)


def divide(a, b):
    assert b[0] > 0 or b[1] < 0, "interval denominator contains zero"
    return mul(a, (1 / b[1], 1 / b[0]))


def check_cell(cell, scale):
    # Reconstruct the full SYMMETRIC matrix from the 15 certified
    # upper-triangle entries. No uncaptured values are invented.
    matrix = [[None] * 5 for _ in range(5)]
    pos = 0
    for i in range(5):
        for j in range(i, 5):
            lo, hi = map(int, cell["upper"][pos])
            assert lo <= hi
            pos += 1
            matrix[i][j] = matrix[j][i] = (
                Fraction(lo, scale), Fraction(hi, scale))
    assert pos == 15

    # Exact rational interval Schur elimination. At each step only
    # the trailing block is needed for the subsequent pivot values.
    for k in range(5):
        pivot = matrix[k][k]
        assert (pivot[0] > 0 if k % 2 == 0 else pivot[1] < 0), (
            f"wrong pivot sign in cell {cell['cell']}, pivot {k + 1}")
        if k < 4:
            new_matrix = [row.copy() for row in matrix]
            for i in range(k + 1, 5):
                for j in range(k + 1, 5):
                    new_matrix[i][j] = sub(
                        matrix[i][j],
                        divide(mul(matrix[i][k], matrix[k][j]), pivot))
            matrix = new_matrix


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input_json", type=Path)
    args = parser.parse_args()
    data = json.loads(args.input_json.read_text(encoding="utf-8"))
    assert data["scale_power_of_two"] == 768
    cells = data["cells"]
    assert len(cells) == 51
    assert Fraction(cells[0]["left"]) == 0
    assert Fraction(cells[-1]["right"]) == Fraction(145, 256)
    for idx, cell in enumerate(cells):
        assert cell["cell"] == idx + 1
        assert len(cell["upper"]) == 15
        if idx:
            assert Fraction(cells[idx - 1]["right"]) == Fraction(cell["left"])
        check_cell(cell, 1 << 768)
    print("PASS: all 255 pivot signs replayed from exported matrices using exact rational interval arithmetic")


if __name__ == "__main__":
    main()
