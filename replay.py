#!/usr/bin/env python3
"""Exact arithmetic replay of Chen–Engel–Glotzer 2010, arXiv v3 Theorem 1.

An accepted pair has an explicit nonzero separating normal. Lattice-coordinate
boxes bound all shifts at which the closed tetrahedra could meet. This is a
Python replay of the published construction, not a proof-assistant certificate.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, product
from math import ceil, floor


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def scale(s, a):
    return tuple(s * x for x in a)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def cross(a, b):
    x, y, z = a
    u, v, w = b
    return (y * w - z * v, z * u - x * w, x * v - y * u)


def det(a, b, c):
    return dot(a, cross(b, c))


def translate(vertices, displacement):
    return tuple(add(v, displacement) for v in vertices)


def edges(vertices):
    return tuple(sub(y, x) for x, y in combinations(vertices, 2))


def normals(vertices):
    return tuple(cross(sub(y, x), sub(z, x)) for x, y, z in combinations(vertices, 3))


def candidate_axes(left, right):
    return (*normals(left), *normals(right),
            *(cross(a, b) for a, b in product(edges(left), edges(right))))


def separating_axis(left, right):
    for n in candidate_axes(left, right):
        if not any(n):
            continue
        a = [dot(n, v) for v in left]
        b = [dot(n, v) for v in right]
        gap = max(min(a) - max(b), min(b) - max(a))
        if gap >= 0:
            return n, gap
    return None


@dataclass
class Replay:
    tetra_count: int
    squared_edge: Fraction
    tetra_volume: Fraction
    cell_volume: Fraction
    checks: int = 0
    zero_gap_witnesses: int = 0
    max_shift: int = 0
    missing_axis: object = None

    @property
    def density(self):
        return self.tetra_count * self.tetra_volume / self.cell_volume


def replay(lattice, tetrahedra, *, on_separation=None):
    a, b, c = lattice
    determinant = det(a, b, c)
    assert determinant and tetrahedra
    lengths = {dot(e, e) for tetra in tetrahedra for e in edges(tetra)}
    assert len(lengths) == 1 and min(lengths) > 0
    volumes = {abs(det(*(sub(v, t[0]) for v in t[1:]))) / Fraction(6)
               for t in tetrahedra}
    assert len(volumes) == 1 and min(volumes) > 0
    result = Replay(len(tetrahedra), min(lengths), min(volumes), abs(determinant))
    dual = tuple(scale(1 / Fraction(determinant), u)
                 for u in (cross(b, c), cross(c, a), cross(a, b)))
    bounds = [[(min(dot(f, v) for v in tetra), max(dot(f, v) for v in tetra))
               for f in dual] for tetra in tetrahedra]

    for i, j in product(range(len(tetrahedra)), repeat=2):
        # If x = y + B*k belongs to both closed hulls, then B^{-1}x -
        # B^{-1}y is k. Its three coordinates belong to these differences.
        ranges = [range(ceil(lo_i - hi_j), floor(hi_i - lo_j) + 1)
                  for (lo_i, hi_i), (lo_j, hi_j) in zip(bounds[i], bounds[j])]
        for k in product(*ranges):
            if i == j and k == (0, 0, 0):
                continue
            shift = add(add(scale(k[0], a), scale(k[1], b)), scale(k[2], c))
            result.checks += 1
            result.max_shift = max(result.max_shift, *map(abs, k))
            cert = separating_axis(tetrahedra[i], translate(tetrahedra[j], shift))
            if cert is None:
                result.missing_axis = (i, j, k)
                return result
            if on_separation is not None:
                on_separation(i, j, k, cert[0])
            if cert[1] == 0:
                result.zero_gap_witnesses += 1
    return result


def ceg_cell():
    # Eq. (1), Definition 2, and Theorem 1, Eqs. (15)–(16).
    o, p, q, r, s = (2, 2, 2), (2, -1, -1), (-1, 2, -1), (-1, -1, 2), (-2, -2, -2)
    positive = ((o, p, q, r), (s, p, q, r))
    a = scale(Fraction(3, 320), (290, 107, -7))
    b = scale(Fraction(3, 320), (-34, 277, 135))
    c = scale(Fraction(3, 320), (94, -83, 247))
    d = scale(Fraction(1, 320), (38, 5, -25))
    negative = tuple(tuple(sub(add(d, a), v) for v in t) for t in positive)
    return (add(a, b), add(b, c), add(c, a)), positive + negative


def main():
    # CEG arXiv v3 Appendix D, D1. A separate one-particle benchmark.
    u = Fraction(-1, 3)
    single = replay(((2, u, u), (u, 2, u), (u, u, 2)),
                    (((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)),))
    assert single.missing_axis is None and single.density == Fraction(18, 49)
    print("one-particle benchmark:", single)
    print("one-particle density:", single.density)

    lattice, tetrahedra = ceg_cell()
    base = replay(lattice, tetrahedra)
    assert base.missing_axis is None and base.density == Fraction(4000, 4671)
    print("published cell:", base)
    print("density:", base.density)

    a, b, c = lattice
    skew = replay((add(a, scale(3, b)), b, c), tetrahedra)
    assert skew.missing_axis is None and skew.density == base.density and skew.max_shift > 1
    print("same lattice in a skew basis:", skew)

    duplicate = replay(lattice, (tetrahedra[0], tetrahedra[0], *tetrahedra[2:]))
    assert duplicate.missing_axis is not None
    print("negative control, duplicate rejected at:", duplicate.missing_axis)

    duplicate_at_distance = translate(tetrahedra[0], scale(3, b))
    shifted = replay(lattice, (tetrahedra[0], duplicate_at_distance, *tetrahedra[2:]))
    assert shifted.missing_axis == (0, 1, (0, -3, 0))
    print("negative control, duplicate through a remote translate:", shifted.missing_axis)


if __name__ == "__main__":
    main()
