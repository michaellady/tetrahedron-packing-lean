"""Compute exact separating-plane margins for a perturbed periodic cell.

The radius is a per-coordinate absolute error in fractional coordinates.
The actual cell can have any invertible basis if its vertices, expressed
in that basis, satisfy this bound against the nominal fractional vertices.
"""

import os
import subprocess
from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from itertools import chain, combinations, combinations_with_replacement, product
from math import ceil, floor, gcd, lcm
from pathlib import Path

from benchmarks.approximant import cell as approximant_cell, read_table
from replay import add, candidate_axes, ceg_cell, cross, det, dot, scale, sub, translate


def expand(lattice, pieces, factor):
    """Scale the period vectors and centroids, keeping the shapes fixed."""
    centers = [tuple(sum(column) / Fraction(4) for column in zip(*v)) for v in pieces]
    return (
        tuple(scale(factor, vector) for vector in lattice),
        tuple(translate(v, scale(factor - 1, c)) for v, c in zip(pieces, centers)),
    )


def inverse_rows(lattice):
    a, b, c = lattice
    inverse_det = 1 / Fraction(det(a, b, c))
    return tuple(scale(inverse_det, row) for row in (cross(b, c), cross(c, a), cross(a, b)))


def fractional_coordinates(lattice, pieces):
    dual = inverse_rows(lattice)
    return tuple(tuple(tuple(dot(row, x) for row in dual) for x in piece) for piece in pieces)


def coordinate_bounds(piece):
    return tuple((min(xs), max(xs)) for xs in zip(*piece))


def shift_ranges(left_bounds, right_bounds, radius):
    return [range(ceil(lo_i - hi_j - 2 * radius), floor(hi_i - lo_j + 2 * radius) + 1)
            for (lo_i, hi_i), (lo_j, hi_j) in zip(left_bounds, right_bounds)]


def axis_margins(left, right, axes=None):
    for axis in candidate_axes(left, right) if axes is None else axes:
        size = sum(map(abs, axis))
        if size == 0:
            continue
        aa, bb = [dot(axis, v) for v in left], [dot(axis, v) for v in right]
        forward, backward = min(bb) - max(aa), min(aa) - max(bb)
        if forward >= backward:
            yield axis, Fraction(forward, 2 * size)
        else:
            yield scale(-1, axis), Fraction(backward, 2 * size)


def clearance(pieces, search_radius):
    """Return a certified lower radius, limiting pair, and number of tested shifts.

    The search box covers the input radius. Its answer can be smaller when
    a separating plane has insufficient margin. A missing plane means the
    calculation supplies no positive tolerance or nonoverlap conclusion.
    """
    bounds = [coordinate_bounds(piece) for piece in pieces]
    radius = search_radius
    limiting_pair = None
    checked = 0
    for i, j in combinations_with_replacement(range(len(pieces)), 2):
        for shift in product(*shift_ranges(bounds[i], bounds[j], search_radius)):
            if i == j and shift <= (0, 0, 0):
                continue
            checked += 1
            left, right = pieces[i], translate(pieces[j], shift)
            best = None
            for _, bound in axis_margins(left, right):
                if best is None or best < bound:
                    best = bound
                if best >= radius:
                    break
            if best is None or best < 0:
                return None, (i, j, shift), checked
            if best < radius:
                radius, limiting_pair = best, (i, j, shift)
    return radius, limiting_pair, checked


def integer_witnesses(vertices, reference, scale_unit, radius):
    """Generate one oriented primitive integer normal per required shift."""
    bounds = [tuple(tuple(Fraction(x, scale_unit) for x in pair)
                    for pair in coordinate_bounds(piece)) for piece in vertices]
    fractional_radius = Fraction(radius, scale_unit)
    count = len(vertices)
    rows = [[[] for _ in vertices] for _ in vertices]
    for i, j in combinations_with_replacement(range(count), 2):
        for shift in product(*shift_ranges(bounds[i], bounds[j], fractional_radius)):
            if i == j and shift <= (0, 0, 0):
                continue
            left = vertices[i]
            right = translate(vertices[j], scale(scale_unit, shift))
            axes = chain(candidate_axes(left, right), candidate_axes(reference[i], reference[j]))
            witness = next((axis for axis, margin in axis_margins(left, right, axes)
                            if radius <= margin), None)
            if witness is None:
                raise ValueError(f"No direction with the required margin for {(i, j, shift)}")
            denominator = lcm(*(x.denominator for x in witness))
            integer_axis = tuple(int(x * denominator) for x in witness)
            divisor = gcd(*integer_axis)
            normal = tuple(x // divisor for x in integer_axis)
            rows[i][j].append((shift, normal))
            rows[j][i].append((scale(-1, shift), scale(-1, normal)))
    return rows


def lean_vector(items):
    return "![" + ", ".join(str(item) for item in items) + "]"


def lean_index_table(name, item_type, items, private=False):
    """Write a finite-index table."""
    count = len(items)
    visibility = "private " if private else ""
    return [
        f"{visibility}def {name} : Fin {count} → {item_type} := ![",
        ",\n".join("  " + value for value in items),
        "]",
        "",
    ]


def emit_lean(path, pieces, scale_unit, radius, namespace):
    """Round down each fractional coordinate and emit kernel-checkable data."""
    if not pieces:
        raise ValueError("Expected at least one tetrahedron")
    vertices = [tuple(tuple(floor(x * scale_unit) for x in v) for v in piece) for piece in pieces]
    rows = integer_witnesses(vertices, pieces, scale_unit, radius)
    count = len(vertices)
    defs = [
        "import TetrahedronPacking.ClearanceCertificate",
        "",
        "/-! Generated by `python3 -m benchmarks.clearance`. The kernel checks each",
        "oriented witness in the applicable shift box before using the general theorem. -/",
        "",
        f"namespace TetrahedronPacking.{namespace}",
        "",
        "open Set",
        "",
    ]
    defs.extend(lean_index_table("vertices", "Fin 4 → Fin 3 → ℤ",
                                 [lean_vector(lean_vector(v) for v in piece) for piece in vertices]))
    fractions = [
        "![\n" + ",\n".join("    " + lean_vector(f"({x.numerator}, {x.denominator})" for x in v)
                             for v in piece) + "\n  ]"
        for piece in pieces
    ]
    defs.extend(lean_index_table("fractions", "Fin 4 → Fin 3 → ℤ × ℤ", fractions, private=True))
    first = vertices[0][0][0]
    n, d = pieces[0][0][0].as_integer_ratio()
    defs.extend([
        f"def reference (i : Fin {count}) (a : Fin 4) (r : Fin 3) : ℚ :=",
        "  ((fractions i a r).1 : ℚ) / ((fractions i a r).2 : ℚ)",
        "",
        f"example : vertices 0 0 0 = {first} ∧ vertices 0 0 0 ≠ {first + 1} := by decide",
        f"example : fractions 0 0 0 = ({n}, {d}) ∧ (fractions 0 0 0).1 ≠ {n + 1} := by decide",
        f"example : reference 0 0 0 = ({n} : ℚ) / {d} := rfl",
        "",
    ])
    data, proof_rows = defs, []
    entry_type = "List ((Fin 3 → ℤ) × (Fin 3 → ℤ))"
    for i, row in enumerate(rows):
        defs = []
        pairs = [", ".join(f"({lean_vector(k)}, {lean_vector(n)})" for k, n in entry)
                 for entry in row]
        defs.extend(lean_index_table(f"axes{i}", entry_type, ["[" + entry + "]" for entry in pairs],
                                     private=True))
        defs.extend([
            *(["set_option maxRecDepth 4096 in", "set_option maxHeartbeats 800000 in"]
              if count > 32 else []),
            f"private theorem checked{i} : ∀ j : Fin {count},",
            f"    checkClearancePair (vertices {i}) (vertices j) {scale_unit} {2 * radius}",
            f"      (decide (({i} : Fin {count}) = j)) (axes{i} j) = true := by decide +kernel",
            "",
        ])
        defs.extend([
            f"private theorem rounded{i} : ∀ (a : Fin 4) (r : Fin 3),",
            f"    let (n, m) := fractions {i} a r",
            f"    0 < m ∧ |n * {scale_unit} - vertices {i} a r * m| ≤ m := by decide",
            "",
        ])
        proof_rows.append(defs)
    defs = [
        f"theorem quantization_bound (i : Fin {count}) (a : Fin 4) (r : Fin 3) :",
        f"    |reference i a r - (vertices i a r : ℚ) / {scale_unit}| ≤ (1 : ℚ) / {scale_unit} := by",
        "  fin_cases i",
    ]
    defs.extend(f"  · exact rational_quantization_bound (rounded{i} a r).1 (by decide)"
                f" (rounded{i} a r).2" for i in range(count))
    defs.append("")
    defs.extend([
        f"theorem disjoint_within_clearance (C : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))",
        f"    (u : Fin {count} → Fin 4 → Fin 3 → ℝ)",
        f"    (hδ : ∀ i a r, |u i a r - (vertices i a r : ℝ) / {scale_unit}| ≤",
        f"      ({radius} : ℝ) / {scale_unit})",
        f"    (i j : Fin {count}) (k : Fin 3 → ℤ) (hk : i ≠ j ∨ k ≠ 0) :",
        "    Disjoint (interior (convexHull ℝ (range (fun a => C.symm (u i a)))))",
        "      (interior (convexHull ℝ (range (fun a => C.symm (u j a) +",
        "        C.symm (fun r => (k r : ℝ)))))) := by",
        "  fin_cases i",
    ])
    for i in range(count):
        defs.extend([
            f"  · exact disjoint_interiors_of_checkClearancePair C vertices u {i} j",
            f"      (d := {scale_unit}) (ε := {radius}) (by decide) (by decide) hδ",
            f"      (axes{i} j) (checked{i} j) k hk",
        ])
    defs.extend([
        "",
        "theorem disjoint_near_reference (C : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))",
        f"    (u : Fin {count} → Fin 4 → Fin 3 → ℝ)",
        f"    (hδ : ∀ i a r, |u i a r - (reference i a r : ℝ)| ≤",
        f"      ({radius} - 1 : ℝ) / {scale_unit})",
        f"    (i j : Fin {count}) (k : Fin 3 → ℤ) (hk : i ≠ j ∨ k ≠ 0) :",
        "    Disjoint (interior (convexHull ℝ (range (fun a => C.symm (u i a)))))",
        "      (interior (convexHull ℝ (range (fun a => C.symm (u j a) +",
        "        C.symm (fun r => (k r : ℝ)))))) := by",
        "  apply disjoint_within_clearance C u _ i j k hk",
        "  intro p a r",
        f"  simpa using clearance_of_quantized_coordinate _ _ _ {scale_unit} {radius}",
        "    (quantization_bound p a r) (hδ p a r)",
        "",
        f"theorem pairwise_disjoint_near_reference (C : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))",
        f"    (u : Fin {count} → Fin 4 → Fin 3 → ℝ)",
        f"    (hδ : ∀ i a r, |u i a r - (reference i a r : ℝ)| ≤",
        f"      ({radius} - 1 : ℝ) / {scale_unit}) :",
        f"    let piece (p : Fin {count} × (Fin 3 → ℤ)) :=",
        "      convexHull ℝ (range (fun a => C.symm (u p.1 a) +",
        "        C.symm (fun r => (p.2 r : ℝ))))",
        "    Pairwise fun p q => Disjoint (interior (piece p)) (interior (piece q)) := by",
        "  exact pairwise_disjoint_of_relative_shift C (fun i a => C.symm (u i a))",
        "    (disjoint_near_reference C u hδ)",
        "",
        "#print axioms quantization_bound",
        "#print axioms disjoint_within_clearance",
        "#print axioms disjoint_near_reference",
        "#print axioms pairwise_disjoint_near_reference",
        "",
                 f"end TetrahedronPacking.{namespace}", ""])
    sources = write_lean_sources(path, data, proof_rows, defs, namespace)
    return sum(len(entries) for row in rows for entries in row), sources


def write_lean_sources(path, data, rows, results, namespace):
    """Use independent proof modules for large tables."""
    if len(rows) <= 32:
        path.write_text("\n".join((*data, *(line for row in rows for line in row), *results)),
                        encoding="utf-8")
        return [], [], path
    end = f"end TetrahedronPacking.{namespace}\n"

    def write_module(name, body):
        module = path.with_name(name + ".lean")
        module.write_text("\n".join(body), encoding="utf-8")
        return module

    data_path = write_module(namespace + "Data", [
        *(line.removeprefix("private ") for line in data), end
    ])
    witness_paths = []
    for i in range(0, len(rows), 4):
        witness_paths.append(write_module(f"{namespace}Witnesses{i // 4}", [
            f"import {data_path.stem}", "", f"namespace TetrahedronPacking.{namespace}", "",
            *(line.removeprefix("private ") for row in rows[i:i + 4] for line in row),
            end,
        ]))
    path.write_text("\n".join([
        *(f"import {module.stem}" for module in witness_paths),
        "", f"namespace TetrahedronPacking.{namespace}", "", "open Set", "", *results,
    ]), encoding="utf-8")
    return [data_path], witness_paths, path


def check_lean_sources(sources, jobs):
    prerequisites, witness_shards, endpoint = sources
    subprocess.run(["lake", "build", "TetrahedronPacking.ClearanceCertificate"], check=True)
    lean_env = os.environ.copy()
    lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], text=True).strip()
    directory = endpoint.resolve().parent
    lean_env["LEAN_PATH"] = os.pathsep.join([str(directory), lean_path])

    def check(source):
        cmd = ["lean", "-j1", "-R", str(directory), "-o", str(source.with_suffix(".olean")),
               str(source)]
        result = subprocess.run(cmd, env=lean_env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(result.stdout, end="", flush=True)
        result.check_returncode()

    for source in prerequisites:
        check(source)
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        list(executor.map(check, witness_shards))
    check(endpoint)


def check_dimer_controls(search_radius):
    lattice, pieces = ceg_cell()
    nominal = fractional_coordinates(lattice, pieces)
    if clearance(nominal, search_radius)[0] != 0:
        raise ValueError("The contact dimer should have zero margin")
    _, compressed = expand(lattice, pieces, Fraction(999, 1000))
    # In each face-sharing dimer particle, the origin has positive
    # barycentric weights after symmetric inward movement of the centroids.
    apex = Fraction(1, 4000)
    weights = (apex,) + ((1 - apex) / 3,) * 3
    if any(w <= 0 for w in weights) or sum(weights) != 1:
        raise ValueError("Invalid overlap witness weights")
    for piece in compressed[:2]:
        if any(dot(weights, column) != 0 for column in zip(*piece)):
            raise ValueError("The compressed pieces do not contain the claimed point")
        if det(*(sub(v, piece[0]) for v in piece[1:])) == 0:
            raise ValueError("Overlap witness requires full-dimensional pieces")
    print("dimer controls: zero nominal margin; exact shared interior point after compression", flush=True)


def rounding_radius_squared(lattice, pieces, search_radius):
    """Lower bound for a common Cartesian ball added to every tetrahedron."""
    fractional = fractional_coordinates(lattice, pieces)
    bounds = [coordinate_bounds(piece) for piece in fractional]
    fractional_radius = search_radius * max(sum(map(abs, row)) for row in inverse_rows(lattice))
    squared = search_radius**2
    limit = None
    for i, j in combinations_with_replacement(range(len(pieces)), 2):
        for k in product(*shift_ranges(bounds[i], bounds[j], fractional_radius)):
            if i == j and k <= (0, 0, 0):
                continue
            shift = tuple(dot(row, k) for row in zip(*lattice))
            best = None
            for axis, margin in axis_margins(pieces[i], translate(pieces[j], shift)):
                if margin < 0:
                    continue
                # Recover gap / 2 from the sup-norm margin and normalize by the
                # Euclidean length of the normal. The comparison stays rational.
                half_gap = margin * sum(map(abs, axis))
                candidate = half_gap**2 / dot(axis, axis)
                if best is None or best < candidate:
                    best = candidate
                if best >= squared:
                    break
            if best is None:
                return None, (i, j, k)
            if best < squared:
                squared, limit = best, (i, j, k)
    return squared, limit


def dimer_rounding_upper_squared(pieces):
    """Bound the normalized rounding radius using the facing face centroids."""
    a, b = pieces[:2]
    ca, cb = (tuple(sum(column) / Fraction(3) for column in zip(*v[1:]))
              for v in (a, b))
    separation = sub(ca, cb)
    edge = sub(a[0], a[1])
    # The midpoint of ca and cb lies inside both added balls as soon as
    # their radii exceed half the distance between the centroids.
    return dot(separation, separation) / (4 * dot(edge, edge))


def edge_rounding_upper_squared(lattice, pieces, pair):
    """Find an overlap threshold from points on the limiting pair's edges."""
    if pair is None:
        return None
    i, j, k = pair
    displacement = tuple(dot(row, k) for row in zip(*lattice))
    left, right = pieces[i], translate(pieces[j], displacement)
    edge_squared = dot(sub(left[0], left[1]), sub(left[0], left[1]))
    upper = None
    for (a0, a1), (b0, b1) in product(combinations(left, 2), combinations(right, 2)):
        u, v, w = sub(a1, a0), sub(b1, b0), sub(a0, b0)
        aa, ab, bb, aw, bw = dot(u, u), dot(u, v), dot(v, v), dot(u, w), dot(v, w)
        det_gram = aa * bb - ab**2
        if det_gram <= 0:
            continue
        s = Fraction(ab * bw - bb * aw, det_gram)
        t = Fraction(aa * bw - ab * aw, det_gram)
        if 0 <= s <= 1 and 0 <= t <= 1:
            gap = add(w, sub(scale(s, u), scale(t, v)))
            upper = min(dot(gap, gap), upper) if upper is not None else dot(gap, gap)
    return None if upper is None else upper / (4 * edge_squared)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--table", type=Path, help="pdftotext -f 25 -l 26 -layout output")
    parser.add_argument("--expansion", type=Fraction, default=Fraction(1001, 1000))
    parser.add_argument("--search-radius", type=Fraction, default=Fraction(1, 1000))
    parser.add_argument("--emit-lean", type=Path, help="directory for the Lean certificate files")
    parser.add_argument("--controls", action="store_true", help="check nominal and compressed dimer")
    parser.add_argument("--rounding-search", type=Fraction, help="bound ball radius in source units")
    parser.add_argument("--check-lean", type=int, metavar="JOBS",
                        help="kernel-check the generated modules using up to JOBS processes")
    args = parser.parse_args()
    if args.expansion <= 0 or args.search_radius < 0:
        parser.error("Require positive expansion and nonnegative radius")
    if args.rounding_search is not None and args.rounding_search <= 0:
        parser.error("Require a positive ball-radius search bound")
    if args.check_lean is not None and (args.emit_lean is None or args.check_lean <= 0):
        parser.error("Supply --emit-lean and a positive number of Lean jobs")
    if args.controls:
        check_dimer_controls(args.search_radius)

    cells = [("dimer", expand(*ceg_cell(), args.expansion))]
    if args.table is not None:
        cells.append(("approximant", approximant_cell(*read_table(args.table), args.expansion)))
    rounded_bounds = {}
    rounded_uppers = {}
    for name, geometry in cells:
        pieces = fractional_coordinates(*geometry)
        radius, limit, count = clearance(pieces, args.search_radius)
        print(f"{name}: {count} shifts, limiting pair {limit}, exact fractional bound {radius}",
              flush=True)
        if radius is not None:
            chart_norm = max(sum(map(abs, row)) for row in inverse_rows(geometry[0]))
            cartesian = radius / chart_norm
            print(f"  approximate bounds: fractional {float(radius):.12g}, "
                  f"fixed-cell Cartesian {float(cartesian):.12g} in source units", flush=True)
        else:
            return 1
        if args.rounding_search is not None:
            squared, rounding_pair = rounding_radius_squared(*geometry, args.rounding_search)
            if squared is None:
                parser.error(f"No rounding certificate for pair {rounding_pair}")
            edge = sub(geometry[1][0][0], geometry[1][0][1])
            normalized = squared / dot(edge, edge)
            rounded_bounds[name] = normalized
            print(f"  rounding guaranteed for (radius / particle edge)² up to {normalized};"
                  f" limiting pair {rounding_pair}", flush=True)
            upper = (dimer_rounding_upper_squared(geometry[1]) if name == "dimer"
                     else edge_rounding_upper_squared(*geometry, rounding_pair))
            if upper is not None:
                rounded_uppers[name] = upper
                if upper < normalized:
                    raise ValueError("Overlap witness contradicts the separation calculation")
                if upper == normalized:
                    print("  exact rounding threshold: the witness gives overlap for any larger radius",
                          flush=True)
                else:
                    print(f"  squared rounding radius above {upper} produces overlap", flush=True)
        if args.emit_lean is not None:
            scale_unit = 10**9
            # Leave an integer unit of room for rounding every vertex down.
            units = floor(radius * scale_unit) - 1
            if units <= 0:
                parser.error("The geometry has no positive clearance at the chosen scale")
            namespace = name.capitalize() + "Clearance"
            file = args.emit_lean / (namespace + ".lean")
            witnesses, sources = emit_lean(file, pieces, scale_unit, units, namespace)
            print(f"  {file}: {witnesses} oriented witnesses, "
                  f"grid bound {units}/{scale_unit}, reference bound {units - 1}/{scale_unit}",
                  flush=True)
            if args.check_lean is not None:
                check_lean_sources(sources, args.check_lean)
    if "approximant" in rounded_bounds:
        dimer_upper = rounded_uppers["dimer"]
        if args.controls and args.expansion == Fraction(1001, 1000) and (
            args.rounding_search == Fraction(1, 100)
        ):
            if not (
                rounded_bounds["dimer"] == dimer_upper == Fraction(1, 24000000)
                and rounded_bounds["approximant"] == rounded_uppers.get("approximant")
                and dimer_upper < rounded_bounds["approximant"]
            ):
                raise ValueError("The default rounding comparison differs from the checked reference")
        if dimer_upper < rounded_bounds["approximant"]:
            print("approximant's guaranteed squared rounding radius exceeds the dimer's upper bound",
                  flush=True)
            if dimer_upper > 0:
                ratio = rounded_bounds["approximant"] / dimer_upper
                print(f"  ratio is approximately {float(ratio):.12g}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
