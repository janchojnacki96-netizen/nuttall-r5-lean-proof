"""Reproduce the compact order-seven Psi_1 certificate with exact arithmetic.

Read the Lean data for the existing panels and congruence bases. With --output,
write the candidate node, panel and cell data for further Lean replay.
"""
import argparse
import json
import re
from fractions import Fraction as Q
from math import ceil, factorial, floor
from pathlib import Path

sources = Path(__file__).resolve().parents[1] / "Nuttall"
data = (sources / "PsiLastCellGridInputs.lean").read_text()
scale = 2**768
snapshot_scale = 2**90


def multiply(left, right):
    products = [a * b for a in left for b in right]
    return min(products) // scale, -((-max(products)) // scale)


def coefficient_rows():
    auxiliary = [1] + [0] * 36
    for j in range(36):
        following = [
            (4 * auxiliary[k - 1] if k else 0) - (5 + 4 * k) * a
            for k, a in enumerate(auxiliary)
        ]
        yield [(-1)**j * (following[k] - auxiliary[k]) * (scale // 2) for k in range(j + 2)]
        auxiliary = following


def jet_snapshot(inputs):
    exponential, coordinate, gaussian = [
        tuple(value * (scale // snapshot_scale) for value in pair) for pair in inputs
    ]
    powers = [(scale, scale)]
    for _ in range(49):
        powers.append(multiply(powers[-1], gaussian))
    for j, row in enumerate(coefficient_rows()):
        terms = []
        for n in range(8):
            y = tuple(n*n*value for value in coordinate)
            polynomial = (0, 0)
            for c in reversed(row):
                polynomial = tuple(v + c for v in multiply(y, polynomial))
            terms.append(multiply(multiply(y, polynomial), powers[n*n]))
        lo, hi = multiply(exponential, tuple(map(sum, zip(*terms))))
        error = factorial(j)*8**j * (20000*Q(9, 25)**64 / (1-Q(9, 25)))
        yield floor((Q(lo, scale) - error)*snapshot_scale), ceil((Q(hi, scale) + error)*snapshot_scale)


def pairs(text):
    return [tuple(map(int, pair)) for pair in re.findall(r"\((-?\d+), (-?\d+)\)", text)]


nodes = pairs(data.split("private def lastCellInputBox")[0])
panels = pairs(data.split("private def lastCellPanelEndpoints")[1])
rightmost_jet_source = (sources / "PsiLastCellJetData.lean").read_text()
rightmost_psi_jets = pairs(rightmost_jet_source.split("def psiOneLastCellJetSnapshot")[0])
assert len(nodes) == 21 and len(panels) == 7 and len(rightmost_psi_jets) == 36


def round_box(box, denominator):
    lo, hi = box
    return floor(lo*denominator), ceil(hi*denominator)


def round_point(value):
    return floor(value*scale), ceil(value*scale)


def exp_neg_point(value):
    x = round_point(value / 1024)
    partial = (0, 0)
    for k in reversed(range(65)):
        partial = tuple(a+b for a, b in zip(round_point(Q(1, factorial(k))), multiply(x, partial)))
    lo, hi = (Q(endpoint, scale) for endpoint in partial)
    enclosure = round_box((1/(hi+Q(2, 3**65*factorial(65))), 1/lo), scale)
    for _ in range(10):
        enclosure = multiply(enclosure, enclosure)
    return tuple(Q(v, scale) for v in enclosure)


def exp_neg_interval(left, right):
    lo, hi = round_box((exp_neg_point(right)[0], exp_neg_point(left)[1]), 10**23)
    return Q(lo, 10**23), Q(hi, 10**23)


def precise_grid_inputs(t):
    def exp_positive(value):
        lo, hi = exp_neg_interval(value, value)
        return round_box((1/hi, 1/lo), snapshot_scale)

    exp_t = exp_positive(t)
    pi_lo, pi_hi = Q("3.14159265358979323846"), Q("3.14159265358979323847")
    exp_4t = exp_positive(4*t)
    coordinate = round_box(
        (pi_lo*Q(exp_4t[0], snapshot_scale), pi_hi*Q(exp_4t[1], snapshot_scale)),
        snapshot_scale,
    )
    gaussian = round_box(exp_neg_interval(*(Q(v, snapshot_scale) for v in coordinate)), snapshot_scale)
    return exp_t, coordinate, gaussian


def verify_existing_nodes():
    times = (Q(255, 512), Q(1, 2), Q(17, 32), Q(9, 16), Q(19, 32), Q(5, 8), Q(21, 32))
    for i, t in enumerate(times):
        assert tuple(nodes[i*3 : i*3+3]) == precise_grid_inputs(t)


def read_bases():
    source = (sources / "PsiCompactBasisData.lean").read_text()
    source = source.split("def psiOneCompactBasisNumerator (")[0]
    blocks = re.findall(r"#v\[\n((?:    #v\[.*\],?\n){7})  \]", source)
    assert len(blocks) == 67
    return [
        [[int(value) for value in re.findall(r"-?\d+", line)] for line in block.splitlines()]
        for block in blocks
    ]


def multiply_matrix(left, right):
    result = []
    for lhs_row in left:
        result_row = []
        for rhs_column in zip(*right):
            products = []
            for a, b in zip(lhs_row, rhs_column):
                endpoints = [a_i*b_i for a_i in a for b_i in b]
                products.append((min(endpoints)//snapshot_scale, -((-max(endpoints))//snapshot_scale)))
            result_row.append(tuple(map(sum, zip(*products))))
        result.append(result_row)
    return result


def panel(jets, width):
    remainder = factorial(36)*8**36*10**6*width**37 / factorial(37)
    weights = [width**(j+1)/factorial(j+1) for j in range(len(jets))]
    return tuple(
        sum(Q(box[k], snapshot_scale)*weight for box, weight in zip(jets, weights)) + sign*remainder
        for k, sign in enumerate((-1, 1))
    )


def store_node(t):
    inputs = precise_grid_inputs(t)
    return {"t": str(t), "inputs": inputs, "jets": list(jet_snapshot(inputs))}


def integer_product(coefficient, interval):
    lo, hi = interval
    if coefficient < 0:
        return coefficient*hi, coefficient*lo
    return coefficient*lo, coefficient*hi


def integer_basis_left_multiply(basis, matrix):
    return [[tuple(map(sum, zip(*(integer_product(c, entry) for c, entry in zip(row, col)))))
             for col in zip(*matrix)] for row in basis]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Path for the exact certificate data as JSON")
    args = parser.parse_args()
    verify_existing_nodes()
    for i, expected_panel in enumerate(panels):
        jets = list(jet_snapshot(tuple(nodes[i*3 : i*3+3])))
        width = Q(1, 512 if i == 0 else 32)
        lo, hi = panel(jets, width)
        assert Q(expected_panel[0], snapshot_scale) <= lo <= hi <= Q(expected_panel[1], snapshot_scale)
        if i == 0:
            assert all(a <= -hi <= -lo <= b for (a, b), (lo, hi) in zip(rightmost_psi_jets, jets))

    uniform_nodes = [store_node(Q(k, 32)) for k in range(22)]
    uniform_panels = [round_box(panel(node["jets"], Q(1, 32)), snapshot_scale) for node in uniform_nodes]
    uniform_panels[16:22] = panels[1:]
    anchors = [None]*23
    anchors[22] = (Q(0), Q(1, 10**16))
    for i in reversed(range(22)):
        anchors[i] = tuple(
            value + Q(bound, snapshot_scale) for value, bound in zip(anchors[i+1], uniform_panels[i])
        )

    endpoints = [0] + [2*i for i in range(1, 62)] + list(range(123, 129))
    all_cells = []
    basis_denominator_squared = 1024**2
    for index, (left, right, basis_int) in enumerate(zip(endpoints, endpoints[1:], read_bases())):
        center, radius = Q(left+right, 512), Q(right-left, 512)
        anchor_index = (left+right+15)//16
        short_width = Q(anchor_index, 32)-center
        assert 0 <= short_width < Q(1, 32)
        raw = store_node(center)
        jets = raw["jets"]
        correction = panel(jets, short_width)
        corner = round_box(tuple(a+b for a, b in zip(anchors[anchor_index], correction)), snapshot_scale)
        psi_jets = [corner] + [(-hi, -lo) for lo, hi in jets]
        fixed_basis = [[(v*2**80, v*2**80) for v in row] for row in basis_int]
        fixed_transpose = list(zip(*fixed_basis))
        norm = [0]*7
        exact_norm = [0]*7
        for k in range(25):
            scaled = [[round_box(tuple(
                Q(v, snapshot_scale) * Q(1, 16)**(i+j) * radius**k / factorial(k)
                for v in psi_jets[i+j+k]
            ), snapshot_scale) for j in range(7)] for i in range(7)]
            congruence = multiply_matrix(multiply_matrix(fixed_basis, scaled), fixed_transpose)
            left_product = integer_basis_left_multiply(basis_int, scaled)
            exact_congruence = list(zip(*integer_basis_left_multiply(basis_int, list(zip(*left_product)))))
            for i in range(7):
                for j in range(7):
                    diagonal = (-1)**i * snapshot_scale if k == 0 and i == j else 0
                    norm[i] += max(abs(v-diagonal) for v in congruence[i][j])
                    lo, hi = exact_congruence[i][j]
                    assert congruence[i][j][0]*basis_denominator_squared <= lo
                    assert hi <= congruence[i][j][1]*basis_denominator_squared
                    exact_norm[i] += max(abs(v-diagonal*basis_denominator_squared) for v in (lo, hi))
        assert max(norm) < 7*snapshot_scale//10
        assert all(10*n < 7*snapshot_scale*basis_denominator_squared for n in exact_norm)
        all_cells.append({
            "index": index,
            "left": str(Q(left, 256)),
            "right": str(Q(right, 256)),
            "center": raw,
            "anchor_index": anchor_index,
            "width": str(short_width),
            "corner": corner,
            "row_numerators": norm,
            "exact_row_numerators": exact_norm,
        })

    assert len(all_cells) == 67
    assert len({record["t"] for record in uniform_nodes + [cell["center"] for cell in all_cells]}) == 89
    worst_cell = max(all_cells, key=lambda cell: max(cell["row_numerators"]))
    assert worst_cell["index"] == 60
    worst_bound = Q(max(worst_cell["row_numerators"]), snapshot_scale)+Q(7, 10**19)*20_000_000**2
    assert worst_bound < Q(664424843, 10**9)

    if args.output:
        certificate = {
            "scale": snapshot_scale,
            "nodes": uniform_nodes,
            "uniform_panels": uniform_panels,
            "cells": all_cells,
        }
        args.output.write_text(json.dumps(certificate, indent=2)+"\n")
    print("All 67 cells and 469 integer matrix rows pass; norm bound < 664424843/10^9.")


if __name__ == "__main__":
    main()
