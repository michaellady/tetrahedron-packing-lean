# Periodic hard-tetrahedron benchmark

The four-particle dimer crystal provides an exact close-packing reference for
comparing simulation initializers and overlap tests. [Chen, Engel and Glotzer, Definition 2 and Theorem 1](https://arxiv.org/abs/1001.0586v3)

| Fixture | Expected geometry | What it exercises |
| --- | --- | --- |
| [ceg.json](ceg.json) | Disjoint interiors, density `4000/4671` | Boundary contact and a nonorthogonal periodic basis |
| [ceg-remote-duplicate.json](ceg-remote-duplicate.json) | Motif pieces 0 and 1 coincide when piece 1 is shifted by `(0,-3,0)` in lattice coordinates | Overlap across periodic images |

The data use Cartesian triples. Divide every component of every vertex and
period by `coordinate_denominator` to recover the paper's units. For unit
edge length, divide the integer components by `480√2` for these two
fixtures. Each group of four vertices is one tetrahedron. Its coordinates
already encode its placement and orientation. Assign the three entries of
`period_columns` as the columns of the period matrix `B`. The infinite
packing adds `B k` to each tetrahedron for every integer triple `k`.
Representatives may lie outside the chosen primary cell.

From the repository root, replay both files with Python's standard library.

```sh
python3 benchmarks/check.py
```

## Check the exact geometry in Lean

Run this command in the pinned Lean environment from the repository root.
Lake tracks both JSON files as byte-level build inputs, so a fixture-only
change also rechecks the matching theorem.

```sh
lake build TetrahedronPacking.PublishedInput TetrahedronPacking.CellScreening
```

The Python replay compares the positive fixture to the paper's coordinate
formulas and checks both files with rational arithmetic. In
[`PublishedInput.lean`](../TetrahedronPacking/PublishedInput.lean), the kernel
compares the embedded fixture bytes to the canonical JSON of the checked
integer data. It checks regularity, the matrix inverse and every required
periodic separation, proves the spatial density, and checks rejection of the
duplicate. The Lean calculation uses integer coordinate units. Multiplying
all coordinates by a positive length unit changes each volume by the same
cubic factor and rescales the radii of the windows used in the limit.

To verify a new fixture, supply the three fields shown in `ceg.json`.
The Python reader accepts JSON integer literals, a positive integer
denominator, a full-rank period matrix for verification, and a nonempty
tetrahedron motif. It rejects duplicate and unknown keys. The generator
normalizes whitespace and key order into a canonical copy, emits proposed
axes and a candidate inverse, and prints the claimed density. Then Lean
rechecks the canonical copy and all the certificates.

```sh
work=$(mktemp -d)
python3 benchmarks/certify.py benchmarks/ceg.json "$work/certificate"
lake env lean "$work/certificate/Certificate.lean"
```

The kernel checks the canonical bytes, so comparing the canonical copy
to any byte-for-byte identical original is direct. For a differently
formatted original, conversion from original JSON to the canonical copy
uses Python's parser. A missing candidate axis stops certificate generation
and reports the pair and shift. The mathematical checker certifies successful
separation. A failed search alone gives no geometric verdict about an
arbitrary input.

To screen regular cells before searching for axes, pass `--screen-only`.
For `m` congruent regular tetrahedra, common squared edge length `s` and
absolute period determinant `D`, the volume ratio exceeds the reference
exactly when

```text
2 (24000 D)^2 < 4671^2 m^2 s^3
```

The [Lean screening theorem](../TetrahedronPacking/CellScreening.lean)
proves the integer comparison. A cell that fails it cannot improve the
record even if all its periodic copies fit. A cell that passes it still
requires a separation certificate.

## Run the HOOMD-blue benchmark

With NumPy and GSD installed, export a frame. For the optional
`--count-overlaps` check install the serial CPU build of HOOMD-blue.
The tests below used HOOMD-blue 7.2.2, GSD 5.0.1 and NumPy 2.5.5.
[HOOMD-blue installation](https://hoomd-blue.readthedocs.io/en/stable/installation.html)

```sh
work=$(mktemp -d)
python3 benchmarks/write_gsd.py benchmarks/ceg.json "$work/contact.gsd" --count-overlaps
python3 benchmarks/write_gsd.py benchmarks/ceg.json "$work/open.gsd" --center-scale 1.001 --count-overlaps
python3 benchmarks/write_gsd.py benchmarks/ceg.json "$work/compressed.gsd" --center-scale 0.999 --count-overlaps
python3 benchmarks/write_gsd.py benchmarks/ceg-remote-duplicate.json "$work/duplicate.gsd" --center-scale 1.001 --count-overlaps
```

The export normalizes to unit particle edge length and transforms both
the vertices and the period matrix to HOOMD's triclinic Cartesian frame.
It wraps each tetrahedron's centroid into the primary box and stores its
centered vertices as a shape with identity orientation. `--center-scale`
scales the lattice and the unwrapped centroids while holding the particle
shape and edge length fixed. The optional engine check runs zero trial
moves and reports the floating-point HPMC overlap count.
[HOOMD-blue box convention](https://hoomd-blue.readthedocs.io/en/stable/hoomd/box.html) · [HPMC overlap test and precision](https://hoomd-blue.readthedocs.io/en/stable/hoomd/hpmc/integrate/hpmcintegrator.html)

The exporter checks edge lengths and period rank with rational arithmetic.
It computes the local vertices, lattice images and wrapped centers before
converting the projected coordinates to floating point. Run the exporter
regressions with `python3 -m unittest discover -s benchmarks -p test_write_gsd.py`.

| Fixture and center scale | Observed CPU HPMC overlaps |
| --- | ---: |
| Published geometry, `1` | 16 |
| Published geometry, `1.001` | 0 |
| Published geometry, `0.999` | 32 |
| Planted duplicate, `1.001` | 1, between tags 0 and 1 |

Lean certifies disjoint interiors for the exact contact geometry. The
export rounds the coordinates and the engine checks overlaps at reduced
precision. Its observed counts characterize this software path and may
vary across platforms. Repeated tags can refer to distinct periodic images.
The expanded positive and duplicate controls provide clearance from the
numerical contact threshold.

## Scientific use and a second published structure

- **Hard-particle statistical physics.** The dimer fixture ties an exact
  volume fraction to coordinates and a periodic overlap test. Phase
  stability depends on free energy. The published simulations report that the
  less dense approximant is favored over the dimer crystal across a broad
  pressure range. [Haji-Akbari, Engel and Glotzer, sections II and III](https://arxiv.org/abs/1106.4765)
- **Colloidal materials and chemistry.** The fixture provides an ideal
  excluded-volume reference for tetrahedral particles. Experiments on gold
  nanotetrahedra observed several superstructures by varying ligand and
  assembly conditions. Density and overlap checks quantify geometry, while
  ligand interactions and assembly kinetics require a physical model.
  [Gold nanotetrahedron experiments](https://doi.org/10.1021/jacs.2c03196)
- **Computational geometry.** A numerical search proposes a cell. The
  integer test discards candidates with insufficient volume ratio, and the
  proof checks the candidate's regularity and all periodic separations.
  Practical scaling depends on motif size, shift-box size and the number of
  candidate axes.

The published 82-particle quasicrystal approximant is a distinct periodic
cell. Its table gives a box, centers and rounded scalar-first quaternions.
Using each displayed quaternion divided by its norm means the exact
rotation matrix can be formed by dividing its quadratic numerator by the
squared norm. On the unexpanded displayed box, the rational replay checked
3,558 pair shifts, found separation in every case and reproduced the
published volume fraction `0.8478659094` to the displayed precision. This
is a computed result for the rational reconstruction. Certifying the
82-particle geometry in Lean would be a separate performance problem.
A sufficient common denominator has 1,531 decimal digits and each piece
pair would otherwise search a shared list of candidate axes. Pair-specific
witnesses would let the checker test fewer axes. The separately reported
656-particle compression at about 0.8503 uses different coordinate data.
[Haji-Akbari et al., methods and supplementary table on PDF pages 25–26](https://arxiv.org/pdf/1012.5138v1)

```sh
work=$(mktemp -d)
curl -fL https://arxiv.org/pdf/1012.5138v1 -o "$work/tetrahedra-phases.pdf" &&
  printf '%s  %s\n' '56be93178c3d9944f55e0e664b46e8750b0500545bc88826d9f67c96a286f433' \
    "$work/tetrahedra-phases.pdf" | sha256sum -c - &&
  pdftotext -f 25 -l 26 -layout "$work/tetrahedra-phases.pdf" "$work/tetrahedra-table.txt" &&
  python3 -m benchmarks.approximant "$work/tetrahedra-table.txt"
```

The unexpanded replay also checks its exact rational density and separation
count against the recorded reference values.
