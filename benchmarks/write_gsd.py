"""Export a periodic tetrahedron fixture for HOOMD-blue HPMC."""

from argparse import ArgumentParser
from fractions import Fraction
from math import floor, isfinite, sqrt
from pathlib import Path

import gsd.hoomd
import numpy as np

if __package__:
    from .check import load_cell, regular_cell_dimensions
else:
    from check import load_cell, regular_cell_dimensions

from replay import cross, dot, scale, sub


def triclinic_geometry(periods, pieces, squared_edge, determinant):
    a, b, c = periods
    if determinant < 0:
        c = scale(-1, c)

    dual_numerators = (cross(b, c), cross(c, a), cross(a, b))
    normal = dual_numerators[2]
    axes = (a, cross(normal, a), normal)
    squared_units = [dot(axis, axis) * squared_edge for axis in axes]

    def project(vector):
        # Divide by both vector norms using a rational squared ratio. Only
        # the final Cartesian projection needs a floating-point square root.
        result = []
        for axis, squared_unit in zip(axes, squared_units, strict=True):
            component = dot(axis, vector)
            magnitude = sqrt(Fraction(component * component, squared_unit))
            result.append(-magnitude if component < 0 else magnitude)
        return result

    images, positions, shapes = [], [], []
    image_range = np.iinfo(np.int32)
    for piece in pieces:
        center = tuple(sum(axis) / 4 for axis in zip(*piece, strict=True))
        image = tuple(floor(dot(row, center) / abs(determinant) + Fraction(1, 2))
                      for row in dual_numerators)
        if any(i < image_range.min or i > image_range.max for i in image):
            raise ValueError("Particle images exceed the int32 GSD range")
        shift = tuple(dot(image, row) for row in zip(a, b, c, strict=True))
        images.append(image)
        positions.append(project(sub(center, shift)))
        shapes.append([project(sub(vertex, center)) for vertex in piece])
    return np.array([project(a), project(b), project(c)]).T, images, positions, shapes


def make_frame(path, center_scale):
    if not isfinite(center_scale) or center_scale <= 0:
        raise ValueError("Center scale must be finite and positive")
    periods, pieces = load_cell(path)
    squared_edge, determinant = regular_cell_dimensions(periods, pieces)
    triangular, images, positions, shapes = triclinic_geometry(
        periods, pieces, squared_edge, determinant
    )
    lx, ly, lz = np.diag(triangular)
    if min(lx, ly, lz) <= 0:
        raise ValueError("Box or positions exceed the float32 GSD range")
    with np.errstate(over="ignore", under="ignore"):
        wrapped = (np.array(positions) * center_scale).astype(np.float32)
        box = np.array([center_scale * lx, center_scale * ly, center_scale * lz,
                        triangular[0, 1] / ly, triangular[0, 2] / lz,
                        triangular[1, 2] / lz], dtype=np.float32)
    if not np.isfinite(box).all() or not np.isfinite(wrapped).all() or np.any(box[:3] <= 0):
        raise ValueError("Box or positions exceed the float32 GSD range")

    frame = gsd.hoomd.Frame()
    frame.configuration.box = box
    frame.particles.N = len(pieces)
    frame.particles.types = [f"T{i}" for i in range(len(pieces))]
    frame.particles.typeid = np.arange(len(pieces), dtype=np.uint32)
    frame.particles.position = wrapped
    frame.particles.image = np.array(images, dtype=np.int32)
    frame.particles.type_shapes = [
        {"type": "ConvexPolyhedron", "vertices": shape} for shape in shapes
    ]
    return frame


def count_overlaps(path):
    import hoomd

    with gsd.hoomd.open(path, mode="r") as trajectory:
        particles = trajectory[0].particles
    simulation = hoomd.Simulation(device=hoomd.device.CPU(), seed=1)
    simulation.create_state_from_gsd(filename=str(path))
    integrator = hoomd.hpmc.integrate.ConvexPolyhedron()
    for name, shape in zip(particles.types, particles.type_shapes, strict=True):
        integrator.shape[name] = {"vertices": shape["vertices"]}
    simulation.operations.integrator = integrator
    simulation.run(0)
    return hoomd.version.version, integrator.overlaps, integrator.map_overlaps


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--center-scale", type=float, default=1.0,
                        help="scale the box and particle centers, keeping unit edge lengths")
    parser.add_argument("--count-overlaps", action="store_true",
                        help="also run the HOOMD-blue CPU overlap check without advancing time")
    args = parser.parse_args()
    try:
        frame = make_frame(args.input, args.center_scale)
    except (OSError, OverflowError, ValueError) as error:
        parser.error(str(error))
    with gsd.hoomd.open(args.output, mode="x") as trajectory:
        trajectory.append(frame)
    if args.count_overlaps:
        version, count, pairs = count_overlaps(args.output)
        print(f"HOOMD-blue {version}: {count} overlapping pairs, tags {pairs}")


if __name__ == "__main__":
    main()
