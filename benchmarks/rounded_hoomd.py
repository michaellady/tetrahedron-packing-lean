"""Replay fixed-pose rounded-particle overlap controls in HOOMD-blue."""

from argparse import ArgumentParser
from fractions import Fraction
from math import sqrt
from pathlib import Path

import hoomd

from benchmarks.approximant import cell as approximant_cell, read_table
from benchmarks.clearance import dimer_rounding_upper_squared, expand, rounding_radius_squared
from benchmarks.write_gsd import triclinic_geometry
from replay import add, ceg_cell, det, dot, sub


def prepare(lattice, pieces):
    edge = sub(pieces[0][0], pieces[0][1])
    edge_squared = dot(edge, edge)
    box, images, positions, shapes = triclinic_geometry(
        lattice, pieces, edge_squared, det(*lattice)
    )
    lx, ly, lz = box.diagonal()
    snapshot = hoomd.Snapshot()
    snapshot.configuration.box = [lx, ly, lz, box[0, 1] / ly, box[0, 2] / lz, box[1, 2] / lz]
    snapshot.particles.N = len(pieces)
    snapshot.particles.types = [f"T{i}" for i in range(len(pieces))]
    snapshot.particles.typeid[:] = range(len(pieces))
    snapshot.particles.position[:] = positions
    snapshot.particles.image[:] = images
    squared_radius, _ = rounding_radius_squared(lattice, pieces, Fraction(1, 100))
    if squared_radius is None:
        raise ValueError("The input has no rounding certificate")
    return snapshot, shapes, squared_radius / edge_squared


def count_overlaps(snapshot, shapes, radius):
    simulation = hoomd.Simulation(device=hoomd.device.CPU(), seed=1)
    simulation.create_state_from_snapshot(snapshot)
    integrator = hoomd.hpmc.integrate.ConvexSpheropolyhedron(default_d=0)
    for name, vertices in zip(snapshot.particles.types, shapes, strict=True):
        integrator.shape[name] = {"vertices": vertices, "sweep_radius": radius}
    simulation.operations.integrator = integrator
    simulation.run(0)
    return integrator.overlaps


def binary_input_geometry(snapshot, shapes):
    """Interpret the host box factors, positions and shape coordinates as exact rationals."""
    lx, ly, lz, xy, xz, yz = (Fraction(float(x)) for x in snapshot.configuration.box)
    periods = ((lx, 0, 0), (xy * ly, ly, 0), (xz * lz, yz * lz, lz))
    pieces = []
    for position, shape in zip(snapshot.particles.position, shapes, strict=True):
        center = tuple(Fraction(float(x)) for x in position)
        pieces.append(tuple(add(center, tuple(map(Fraction, v))) for v in shape))
    return periods, tuple(pieces)


def check_binary_input(dimer, approximant, radius):
    squared = Fraction(radius)**2
    _, dimer_pieces = binary_input_geometry(*dimer[:2])
    edge = sub(dimer_pieces[0][0], dimer_pieces[0][1])
    dimer_upper = dimer_rounding_upper_squared(dimer_pieces) * dot(edge, edge)
    approximant_lower, _ = rounding_radius_squared(
        *binary_input_geometry(*approximant[:2]), Fraction(1, 100)
    )
    if approximant_lower is None:
        raise ValueError("No separation certificate for the binary approximant input")
    print("Exact rational check of the binary host inputs at the intermediate radius", flush=True)
    print(f"  dimer overlap witness: {dimer_upper < squared}", flush=True)
    print(f"  approximant nonoverlap certificate: {squared <= approximant_lower}", flush=True)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("table", type=Path, help="pdftotext -f 25 -l 26 -layout output")
    args = parser.parse_args()
    expansion = Fraction(1001, 1000)
    dimer = prepare(*expand(*ceg_cell(), expansion))
    approximant = prepare(*approximant_cell(*read_table(args.table), expansion))
    between = sqrt((dimer[2] + approximant[2]) / 2)
    print(f"HOOMD-blue {hoomd.version.version} CPU, zero trial moves", flush=True)
    for name, (snapshot, shapes, squared_radius) in (("dimer", dimer), ("approximant", approximant)):
        for label, radius in (
            ("95% of threshold", 0.95 * sqrt(squared_radius)),
            ("between thresholds", between),
            ("105% of threshold", 1.05 * sqrt(squared_radius)),
        ):
            overlaps = count_overlaps(snapshot, shapes, radius)
            print(f"{name}, {label}, radius {radius:.12g}: {overlaps} overlaps", flush=True)
    check_binary_input(dimer, approximant, between)


if __name__ == "__main__":
    main()
