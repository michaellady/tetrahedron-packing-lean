#!/usr/bin/env python3
"""Scale the exact Python replay using supercells of the CEG packing."""

from argparse import ArgumentParser
from fractions import Fraction
from itertools import product
from math import gcd, lcm, prod
from time import perf_counter

from replay import add, ceg_cell, dot, replay, scale, sub, translate

REPEATS = ((1, 1, 1), (2, 2, 1), (2, 2, 2), (4, 4, 2), (4, 4, 4))


def supercell(repeats):
    lattice, motif = ceg_cell()
    periods = tuple(scale(count, axis) for count, axis in zip(repeats, lattice))
    copies = []
    for i, j, k in product(*(range(count) for count in repeats)):
        shift = add(add(scale(i, lattice[0]), scale(j, lattice[1])), scale(k, lattice[2]))
        copies.extend(translate(tetra, shift) for tetra in motif)
    return periods, tuple(copies)


def emit_lean(repeats):
    """Emit kernel benchmarks for the generated projections.

    This measures validation of the supplied comparisons. The certificate
    generator still supplies the pair selection and translated offsets.
    """
    periods, pieces = supercell(repeats)
    _, motif = ceg_cell()
    positions = [sub(piece[0], motif[i % 4][0]) for i, piece in enumerate(pieces)]
    terms = []

    def emit(i, j, shift, normal):
        normal = tuple(map(Fraction, normal))
        denominator = lcm(*(x.denominator for x in normal))
        numerators = tuple(int(x * denominator) for x in normal)
        common_divisor = gcd(*numerators)
        axis = tuple(x // common_divisor for x in numerators)
        displacement = sub(positions[j], positions[i])
        for k, period in zip(shift, periods):
            displacement = add(displacement, scale(k, period))
        offset = 160 * dot(axis, displacement)
        assert int(offset) == offset
        vector = ", ".join(map(str, axis))
        terms.append(f"integerSeparates ![{vector}] (recordVertex {i % 4}) "
                     f"(recordVertex {j % 4}) ({int(offset)})")

    outcome = replay(periods, pieces, on_separation=emit)
    assert outcome.missing_axis is None and len(terms) == outcome.checks
    print("import TetrahedronPacking.RecordArithmetic\n")
    print("open TetrahedronPacking Matrix\n")
    print(f"-- {len(pieces)} pieces and {len(terms)} explicit comparisons "
          f"({len(set(terms))} distinct)")
    print("set_option maxRecDepth 10000\n")
    chunk_size = 64
    for start in range(0, len(terms), chunk_size):
        name = f"benchmarkBlock{start // chunk_size}"
        print(f"theorem {name} :")
        print("    ([" + ",\n      ".join(terms[start:start + chunk_size]) + "]).all id = true := by")
        print(f"  decide +kernel\n#print axioms {name}\n")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=int, choices=[4 * prod(r) for r in REPEATS],
                        help="emit a Lean kernel benchmark for this motif size")
    args = parser.parse_args()
    if args.lean is not None:
        emit_lean(next(r for r in REPEATS if 4 * prod(r) == args.lean))
        return
    expected = replay(*ceg_cell()).density
    for repeats in REPEATS:
        periods, pieces = supercell(repeats)
        start = perf_counter()
        outcome = replay(periods, pieces)
        elapsed = perf_counter() - start
        assert outcome.tetra_count == 4 * prod(repeats)
        assert outcome.density == expected and outcome.missing_axis is None
        uniform_box = outcome.tetra_count ** 2 * (2 * outcome.max_shift + 1) ** 3
        uniform_box -= outcome.tetra_count
        print(f"{outcome.tetra_count:3} pieces  {outcome.checks:6} checked pairs  "
              f"{uniform_box:8} uniform box  radius {outcome.max_shift}  {elapsed:7.3f} s",
              flush=True)


if __name__ == "__main__":
    main()
