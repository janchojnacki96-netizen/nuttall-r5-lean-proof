"""Check candidate rank-eight Ψ₂ enclosures on the first 53 compact cells.

Generate the input with preprint_psi_one_compact_probe.py --output. The
basis calculation proposes dyadic integers. All certificate checks use
exact rationals or integers.
"""

import argparse
import json
from decimal import Decimal, localcontext
from fractions import Fraction
from math import factorial
from pathlib import Path

from preprint_psi_one_compact_probe import (
    integer_basis_left_multiply,
    round_box,
    snapshot_scale,
)

BASIS_SCALE = 1024


def weighted_panel(jets, width):
    remainder = 8**36 * 10**6 * width**38 / 38
    weights = [width**(j + 2) / ((j + 2) * factorial(j)) for j in range(36)]
    return tuple(
        sum(Fraction(box[k], snapshot_scale) * w for box, w in zip(jets, weights))
        + sign * remainder
        for k, sign in enumerate((-1, 1))
    )


def extend_two(one_right, two_right, jets, width):
    weighted = weighted_panel(jets, width)
    return tuple(x + width * y + z for x, y, z in zip(two_right, one_right, weighted))


def candidate_basis(jets):
    with localcontext(prec=50):
        lower = [[Decimal(i == j) for j in range(8)] for i in range(8)]
        pivots = []
        for j in range(8):
            diagonal = Decimal(sum(jets[2*j])) / (2 * snapshot_scale * 16**(2*j))
            pivot = diagonal - sum(lower[j][k]**2 * pivots[k] for k in range(j))
            assert (-1)**j * pivot > 0
            pivots.append(pivot)
            for i in range(j + 1, 8):
                value = Decimal(sum(jets[i+j])) / (2 * snapshot_scale * 16**(i+j))
                lower[i][j] = (
                    value - sum(lower[i][k] * lower[j][k] * pivots[k] for k in range(j))
                ) / pivot

        inverse = [[Decimal(i == j) for j in range(8)] for i in range(8)]
        for i in range(8):
            for j in range(i):
                inverse[i][j] = -sum(lower[i][k] * inverse[k][j] for k in range(j, i))
        return [
            [round(value * BASIS_SCALE / abs(pivot).sqrt()) for value in row]
            for row, pivot in zip(inverse, pivots)
        ]


def check_cell(cell, one, two):
    anchor = cell["anchor_index"]
    raw = cell["center"]["jets"]
    corner = round_box(extend_two(one[anchor], two[anchor], raw, Fraction(cell["width"])),
                       snapshot_scale)
    jets = [corner, tuple(-v for v in reversed(cell["corner"]))] + raw
    basis = candidate_basis(jets)
    assert all(row[i] and not any(row[i+1:]) for i, row in enumerate(basis))
    weight = max(sum(abs(x) for x in row) for row in basis)
    assert weight < BASIS_SCALE * 6_700_000

    radius = (Fraction(cell["right"]) - Fraction(cell["left"])) / 2
    assert 0 < radius <= Fraction(1, 256)
    norm = [0] * 8
    denominator = snapshot_scale * BASIS_SCALE**2
    for k in range(24):
        scaled = [
            [
                round_box(
                    tuple(Fraction(v, snapshot_scale * 16**(i+j))
                          * radius**k / factorial(k) for v in jets[i+j+k]),
                    snapshot_scale,
                )
                for j in range(8)
            ]
            for i in range(8)
        ]
        left = integer_basis_left_multiply(basis, scaled)
        congruence = list(zip(*integer_basis_left_multiply(basis, list(zip(*left)))))
        for i, row in enumerate(congruence):
            for j, entry in enumerate(row):
                diagonal = (-1)**i * denominator if i == j and k == 0 else 0
                norm[i] += max(abs(v-diagonal) for v in entry)

    # Apply the entrywise Taylor remainder after the two basis multiplications.
    bound = Fraction(max(norm), denominator) + Fraction(8 * weight**2, BASIS_SCALE**2 * 10**18)
    assert bound < Fraction(559, 1000)
    return bound, {"index": cell["index"], "corner": corner,
                   "basis": basis, "row_numerators": norm}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("psi_one_certificate", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = json.loads(args.psi_one_certificate.read_text())
    assert data["scale"] == snapshot_scale
    assert len(data["nodes"]) == len(data["uniform_panels"]) == 22

    one = [None] * 22 + [(Fraction(0), Fraction(1, 10**16))]
    two = one.copy()
    for i in reversed(range(22)):
        jets = data["nodes"][i]["jets"]
        two[i] = extend_two(one[i+1], two[i+1], jets, Fraction(1, 32))
        one[i] = tuple(x+Fraction(y, snapshot_scale)
                       for x, y in zip(one[i+1], data["uniform_panels"][i]))

    prefix = data["cells"][:53]
    assert [cell["index"] for cell in prefix] == list(range(53))
    assert Fraction(prefix[0]["left"]) == 0 and Fraction(prefix[-1]["right"]) == Fraction(53, 128)
    results = [check_cell(cell, one, two) for cell in prefix]
    worst, cell = max(results, key=lambda result: result[0])
    assert worst < Fraction(559, 1000)
    if args.output:
        output = {"scale": snapshot_scale, "basis_scale": BASIS_SCALE,
                  "cells": [record for _, record in results]}
        args.output.write_text(json.dumps(output, indent=2) + "\n")
    print(f"All 53 candidate cells pass with norm < 559/1000. Worst cell: {cell['index']}.")


if __name__ == "__main__":
    main()
