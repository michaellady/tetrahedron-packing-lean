#!/usr/bin/env python3
"""Test common separating directions over the vertices of the CEG parameter region."""

from fractions import Fraction as Q
from itertools import combinations, product
from math import floor

from replay import add, ceg_cell, cross, det, dot, edges, normals, scale, sub


def cell(u, v, w):
    """arXiv v3 equations (1), (6) and Definition 2."""
    a = (Q(27, 10) + u, Q(21, 20) - v, -Q(3, 20) + 2 * u + v)
    b = (-Q(3, 10) - u, Q(51, 20) + v, Q(27, 20) - 2 * u - v)
    c = (Q(129, 160) - u + 2 * v + 2 * w, -Q(237, 320) + u / 2 - v + 3 * w,
         Q(753, 320) + u / 2 - v + w)
    d = (Q(1, 10) + u, -Q(1, 20) + u + v, -Q(1, 20) + u - v)
    positive = ceg_cell()[1][:2]
    negative = tuple(tuple(sub(add(d, a), vertex) for vertex in tetra) for tetra in positive)
    return (add(a, b), add(b, c), add(c, a)), positive + negative


def shared_axis_failures(points, radius):
    """Finite shifts only. A signed direction must work at every listed parameter vertex."""
    cells = [cell(*point) for point in points]
    shifts = list(product(range(-radius, radius + 1), repeat=3))
    failures = []
    for i, j in product(range(4), repeat=2):
        first, second = (cells[0][1][t] for t in (i, j))
        axes = set(normals(first) + normals(second))
        axes.update(cross(e, f) for e, f in product(edges(first), edges(second)))
        axes.discard((0, 0, 0))
        projections = []
        for n in axes:
            row = []
            for periods, pieces in cells:
                left = [dot(n, v) for v in pieces[i]]
                right = [dot(n, v) for v in pieces[j]]
                row.append((tuple(dot(n, v) for v in periods),
                            min(right) - max(left), max(right) - min(left)))
            projections.append(row)
        for k in shifts:
            if i == j and not any(k):
                continue
            if not any(all(dot(k, lattice) + forward >= 0 for lattice, forward, _ in row) or
                       all(dot(k, lattice) + backward <= 0 for lattice, _, backward in row)
                       for row in projections):
                failures.append((i, j, k))
    return 16 * len(shifts) - 4, failures


def lattice_coordinate_bounds(points):
    """Enclose the Cramer ratios throughout the convex hull of the input points."""
    # The three columns of each Cramer numerator are affine in the parameters.
    # At a convex combination of the corners its determinant is a convex
    # combination of mixed-corner determinants, by multilinearity.
    cells = [cell(*point) for point in points]
    denominator_lower_bound = Q(42039, 1000)  # CEG Lemma 4; also checked in Lean.
    bounds = []
    for axis in range(3):
        numerators = []
        for i, j in product(range(4), repeat=2):
            for choices in product(range(len(cells)), repeat=3):
                columns = [cells[c][1][i][j] if col == axis else cells[c][0][col]
                           for col, c in enumerate(choices)]
                numerators.append(det(*columns))
        bounds.append((min(0, min(numerators)) / denominator_lower_bound,
                       max(0, max(numerators)) / denominator_lower_bound))
    return bounds


def main():
    assert cell(Q(3, 160), Q(3, 64), Q(0)) == ceg_cell()
    corners = [(sign * Q(3, 10), Q(0), Q(3, 64)) for sign in (-1, 1)]
    corners += [(-sign * Q(3, 5), sign * Q(3, 20), -Q(33, 320)) for sign in (-1, 1)]
    crossings = [add(p, scale(-p[0] / (q[0] - p[0]), sub(q, p)))
                 for p, q in combinations(corners, 2) if p[0] * q[0] < 0]
    bounds = lattice_coordinate_bounds(corners)
    radius = max(floor(hi - lo) for lo, hi in bounds)
    print("lattice-coordinate bounds:", ", ".join(f"[{lo}, {hi}]" for lo, hi in bounds))
    print("uniform shift radius:", radius)
    for name, points in (
        ("entire parameter tetrahedron", corners),
        ("u nonnegative", crossings + [p for p in corners if p[0] > 0]),
        ("u nonpositive", crossings + [p for p in corners if p[0] < 0]),
    ):
        checked, failures = shared_axis_failures(points, radius)
        print(f"{name}: {len(points)} parameter vertices, {checked} shift/pair checks, "
              f"{len(failures)} without a shared signed axis")
        if failures:
            print("  unresolved shifts:", sorted({k for _, _, k in failures}))


if __name__ == "__main__":
    main()
