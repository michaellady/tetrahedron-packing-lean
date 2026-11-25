"""Replay fixed-pose rounded-particle overlap controls in HOOMD-blue."""

from argparse import ArgumentParser
from fractions import Fraction
from math import sqrt
from pathlib import Path

import hoomd

from benchmarks.approximant import cell as approximant_cell, read_table
from benchmarks.clearance import expand, rounding_radius_squared
from benchmarks.write_gsd import triclinic_geometry
from replay import ceg_cell, det, dot, sub


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


if __name__ == "__main__":
    main()
