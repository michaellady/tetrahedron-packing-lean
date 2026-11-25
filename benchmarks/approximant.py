"""Replay the published 82-particle approximant with rational arithmetic."""

import re
from argparse import ArgumentParser
from fractions import Fraction
from pathlib import Path

from replay import add, dot, replay, scale


REFERENCE = ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1))
PUBLISHED_DENSITY = Fraction(328000000000000000000000000000000, 386853624316307362350598053221523)
PUBLISHED_SHIFT_CHECKS = 3558


def read_table(path):
    # The table begins on PDF page 25 after the caption, and spans two pages.
    lines = path.read_text(encoding="utf-8").splitlines()
    header = next(i for i in range(len(lines) - 1) if lines[i + 1].strip() == "82")
    lengths = tuple(map(Fraction, lines[header].split()))
    row_pattern = r"\s*[+-]?\d+\.\d+(?:\s+[+-]?\d+\.\d+){6}\s*"
    rows = [tuple(map(Fraction, line.split())) for line in lines[header + 2:]
            if re.fullmatch(row_pattern, line)]
    if len(lengths) != 3 or len(rows) != 82:
        raise ValueError("Expected three box lengths and 82 positions and orientations")
    return lengths, rows


def exact_rotation(a, b, c, d):
    squared_norm = a*a + b*b + c*c + d*d
    # Divide the displayed numerator matrix by q·q so that rounded
    # quaternion entries still represent an exact proper rotation.
    numerator = (
        (a*a + b*b - c*c - d*d, 2*(b*c - a*d), 2*(b*d + a*c)),
        (2*(b*c + a*d), a*a - b*b + c*c - d*d, 2*(c*d - a*b)),
        (2*(b*d - a*c), 2*(c*d + a*b), a*a - b*b - c*c + d*d),
    )
    return tuple(scale(1 / squared_norm, row) for row in numerator)


def cell(lengths, rows, expansion):
    periods = tuple(tuple(expansion * length if i == j else 0 for j in range(3))
                    for i, length in enumerate(lengths))
    pieces = []
    for x, y, z, *quaternion in rows:
        center = scale(expansion, (x, y, z))
        rotation = exact_rotation(*quaternion)
        pieces.append(tuple(add(center, tuple(dot(row, v) for row in rotation))
                            for v in REFERENCE))
    return periods, tuple(pieces)


def packing(lengths, rows, expansion):
    return replay(*cell(lengths, rows, expansion))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("table", type=Path, help="pdftotext -f 25 -l 26 -layout output")
    parser.add_argument("expansion", type=Fraction, nargs="*",
                        help="factors for box lengths and particle centers")
    args = parser.parse_args()
    lengths, rows = read_table(args.table)
    separated = True
    for factor in args.expansion or [Fraction(1)]:
        if factor <= 0:
            parser.error("Expansion factors must be positive")
        result = packing(lengths, rows, factor)
        separated = separated and result.missing_axis is None
        status = ("all separations verified" if result.missing_axis is None
                  else f"missing separating axis {result.missing_axis}")
        print(f"factor {factor}: volume ratio {float(result.density):.12f} "
              f"({result.density}), {result.checks} checks, {status}", flush=True)
        if factor == 1 and result.missing_axis is None and (
            result.density != PUBLISHED_DENSITY or result.checks != PUBLISHED_SHIFT_CHECKS
        ):
            parser.error("Unexpanded cell differs from the expected density or shift count")
    return 0 if separated else 1


if __name__ == "__main__":
    raise SystemExit(main())
