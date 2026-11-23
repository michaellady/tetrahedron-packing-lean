"""Reproduce the exact benchmark cases from their serialized geometry."""

import json
import sys
from fractions import Fraction
from pathlib import Path

BENCHMARK_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(BENCHMARK_DIR.parent))

from replay import ceg_cell, det, dot, edges, replay, scale, translate


def read_input(path):
    def object_without_duplicates(pairs):
        result = dict(pairs)
        if len(result) != len(pairs):
            raise ValueError("Duplicate JSON keys")
        return result

    data = json.loads(path.read_text(encoding="utf-8"),
                      object_pairs_hook=object_without_duplicates)
    if not isinstance(data, dict) or data.keys() != {
        "coordinate_denominator", "period_columns", "tetrahedra"
    }:
        raise ValueError("Expected the three periodic cell fields")
    denominator = data["coordinate_denominator"]
    if type(denominator) is not int or denominator <= 0:
        raise ValueError("Coordinate denominator must be a positive integer")

    def read_vector(components):
        if not isinstance(components, list) or len(components) != 3 or any(
            type(x) is not int for x in components
        ):
            raise ValueError("Expected a Cartesian triple of integers")
        return tuple(components)

    periods = data["period_columns"]
    pieces = data["tetrahedra"]
    if not isinstance(periods, list) or len(periods) != 3 or not isinstance(pieces, list) or (
        not pieces or any(not isinstance(piece, list) or len(piece) != 4 for piece in pieces)
    ):
        raise ValueError("Expected three periods and a nonempty motif of tetrahedra")
    return (denominator, tuple(map(read_vector, periods)),
            tuple(tuple(map(read_vector, piece)) for piece in pieces))


def load_cell(path):
    denominator, periods, pieces = read_input(path)
    unit = Fraction(1, denominator)
    periods = tuple(scale(unit, period) for period in periods)
    pieces = tuple(tuple(scale(unit, vertex) for vertex in piece) for piece in pieces)
    return periods, pieces


def regular_cell_dimensions(periods, pieces):
    squared_lengths = {dot(edge, edge) for piece in pieces for edge in edges(piece)}
    if len(squared_lengths) != 1 or min(squared_lengths) <= 0:
        raise ValueError("Expected congruent regular tetrahedra with positive edge length")
    determinant = det(*periods)
    if determinant == 0:
        raise ValueError("Expected an invertible period matrix")
    return squared_lengths.pop(), determinant


def main():
    periods, pieces = load_cell(BENCHMARK_DIR / "ceg.json")
    if (periods, pieces) != ceg_cell():
        raise SystemExit("ceg.json: coordinates differ from the published cell")
    base = replay(periods, pieces)
    if base.missing_axis is not None:
        raise SystemExit(f"ceg.json: missing separating axis for {base.missing_axis}")
    if base.density != Fraction(4000, 4671):
        raise SystemExit(f"ceg.json: unexpected density {base.density}")
    print(f"ceg.json: density {base.density}, {base.checks} separation checks")

    control_periods, control_pieces = load_cell(BENCHMARK_DIR / "ceg-remote-duplicate.json")
    expected_duplicate = (pieces[0], translate(pieces[0], scale(3, periods[1])), *pieces[2:])
    if control_periods != periods or control_pieces != expected_duplicate:
        raise SystemExit("ceg-remote-duplicate.json: coordinates differ from the expected control")
    rejected = replay(control_periods, control_pieces)
    if rejected.missing_axis != (0, 1, (0, -3, 0)):
        raise SystemExit(f"ceg-remote-duplicate.json: unexpected separation result "
                         f"{rejected.missing_axis}")
    print(f"ceg-remote-duplicate.json: coincident pair {rejected.missing_axis}")


if __name__ == "__main__":
    main()
