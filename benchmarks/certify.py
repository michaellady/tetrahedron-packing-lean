"""Generate a Lean certificate and its canonical JSON from a periodic-cell file."""

import json
from argparse import ArgumentParser
from math import gcd
from pathlib import Path

from check import read_input, regular_cell_dimensions
from replay import cross, replay, scale


def canonical_json(denominator, periods, pieces):
    motif = ",\n".join(f"    {json.dumps(piece)}" for piece in pieces)
    return (
        "{\n"
        f'  "coordinate_denominator": {denominator},\n'
        f'  "period_columns": {json.dumps(periods)},\n'
        f'  "tetrahedra": [\n{motif}\n  ]\n'
        "}\n"
    )


def cell_dimensions(periods, pieces):
    length, determinant = regular_cell_dimensions(periods, pieces)
    beats_record = 2 * (24000 * abs(determinant)) ** 2 < 4671**2 * len(pieces)**2 * length**3
    return length, determinant, beats_record


def lean_certificate(denominator, periods, pieces):
    length, determinant, beats_record = cell_dimensions(periods, pieces)

    axes = set()

    def collect_axis(_i, _j, _k, axis):
        sign = 1 if next(x for x in axis if x) > 0 else -1
        divisor = sign * gcd(*axis)
        axes.add(tuple(x // divisor for x in axis))

    result = replay(periods, pieces, on_separation=collect_axis)
    if result.missing_axis is not None:
        raise ValueError(f"No separating axis for pair and shift {result.missing_axis}")

    a, b, c = periods
    sign = 1 if determinant > 0 else -1
    inverse = [scale(sign, v) for v in (cross(b, c), cross(c, a), cross(a, b))]
    common = gcd(abs(determinant), *(x for row in inverse for x in row))
    inverse = "; ".join(", ".join(str(x // common) for x in row) for row in inverse)

    def lean_vector(parts):
        return "![" + ", ".join(map(str, parts)) + "]"

    period_term = lean_vector(map(lean_vector, periods))
    piece_term = lean_vector(lean_vector(map(lean_vector, piece)) for piece in pieces)
    axes_term = "[" + ", ".join(map(lean_vector, sorted(axes))) + "]"
    density = result.density
    volume_num = 6 * result.tetra_count * result.tetra_volume
    comparison = "4000 * (6 * |cell.periods.det|) < 4671 * cell.volumeNumerator"
    conclusion = comparison if beats_record else f"¬ ({comparison})"
    proof = ("  apply (cell.regular_record_screen _ regular_checks).mpr\n  decide +kernel"
             if beats_record else
             "  rw [cell.regular_record_screen _ regular_checks]\n  decide +kernel")
    return density, f"""import TetrahedronPacking.CellInput
import TetrahedronPacking.CellScreening

namespace GeneratedCertificate
open TetrahedronPacking Filter MeasureTheory Set
open scoped Pointwise Topology

def input : CellInput {len(pieces)} := ⟨{denominator}, {period_term}, {piece_term}⟩

def cell : IntegerCell {len(pieces)} :=
  input.toIntegerCell !![{inverse}] {abs(determinant) // common} {axes_term}

set_option maxRecDepth 20000 in
theorem canonical_json : input.canonicalJson = include_str "cell.json" := by decide +kernel

theorem positive_units : 0 < input.coordinateDenominator := by decide +kernel

theorem inverse_valid : cell.inverseValid := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem separation_checks : ∀ i j, cell.checkPair i j = true := by decide +kernel

theorem regular_checks : ∀ i, cell.checkRegular {length} i = true := by decide +kernel

theorem disjoint_interiors :
    let L := Submodule.span ℤ (range (cell.basis inverse_valid))
    Pairwise fun p q : Fin {len(pieces)} × L =>
      Disjoint (interior ((p.2 : Fin 3 → ℝ) +ᵥ cell.piece p.1))
        (interior ((q.2 : Fin 3 → ℝ) +ᵥ cell.piece q.1)) :=
  cell.pairwise_disjoint_of_checks inverse_valid separation_checks

set_option maxHeartbeats 2000000 in
theorem spatial_density :
    let L := Submodule.span ℤ (range (cell.basis inverse_valid))
    Tendsto (fun R : ℝ =>
      volume.real ((⋃ p : Fin {len(pieces)} × L, (p.2 : Fin 3 → ℝ) +ᵥ cell.piece p.1) ∩
        Metric.closedBall 0 R) / volume.real (Metric.closedBall (0 : Fin 3 → ℝ) R))
      atTop (𝓝 ({density.numerator} / {density.denominator} : ℝ)) := by
  have hn : cell.volumeNumerator = {volume_num} := by decide +kernel
  have hd : |cell.periods.det| = {abs(determinant)} := by decide +kernel
  have h := cell.spatial_density_of_checks inverse_valid separation_checks
  rw [hn, hd] at h
  have ratio : (({volume_num} : ℤ) : ℝ) / (6 * (({abs(determinant)} : ℤ) : ℝ)) =
      {density.numerator} / {density.denominator} := by norm_num
  simpa only [ratio] using h

theorem record_comparison : {conclusion} := by
{proof}

#print axioms canonical_json
#print axioms regular_checks
#print axioms disjoint_interiors
#print axioms spatial_density
#print axioms record_comparison

end GeneratedCertificate
"""


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path, nargs="?",
                        help="new directory for the generated certificate")
    parser.add_argument("--screen-only", action="store_true",
                        help="compare the volume ratio with the record before overlap checking")
    args = parser.parse_args()
    if args.screen_only:
        if args.output is not None:
            parser.error("--screen-only takes only the input path")
        try:
            _, periods, pieces = read_input(args.input)
            _, _, beats_record = cell_dimensions(periods, pieces)
        except (OSError, ValueError) as error:
            parser.error(str(error))
        if beats_record:
            print("Volume ratio exceeds 4000/4671. Periodic separation still needs checking.")
        else:
            print("Volume ratio is at most 4000/4671.")
        return
    if args.output is None:
        parser.error("Specify an output directory or use --screen-only")
    if args.output.exists():
        parser.error("The output directory already exists")
    try:
        data = read_input(args.input)
        density, source = lean_certificate(*data)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    args.output.mkdir()
    (args.output / "cell.json").write_text(canonical_json(*data), encoding="utf-8")
    (args.output / "Certificate.lean").write_text(source, encoding="utf-8")
    print(f"Candidate density {density}. Run lake env lean {args.output / 'Certificate.lean'}")


if __name__ == "__main__":
    main()
