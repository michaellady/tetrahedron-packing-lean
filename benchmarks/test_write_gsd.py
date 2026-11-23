"""Regression tests for exact preprocessing before GSD export."""

import json
from math import sqrt
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest import TestCase

import numpy as np

from write_gsd import make_frame


class GSDExportTests(TestCase):
    def frame(self, periods, vertices):
        with TemporaryDirectory() as directory:
            path = Path(directory) / "cell.json"
            path.write_text(json.dumps({
                "coordinate_denominator": 1,
                "period_columns": periods,
                "tetrahedra": [vertices],
            }), encoding="utf-8")
            return make_frame(path, 1)

    def test_remote_lattice_translation_preserves_exported_geometry(self):
        period = 2**26
        periods = [(period, 0, 0), (0, period, 0), (0, 0, period)]
        vertices = [(19, 19, 19), (19, 13, 13), (13, 19, 13), (13, 13, 19)]
        origin = self.frame(periods, vertices)
        remote = self.frame(periods, [
            tuple(coordinate + 2**54 for coordinate in vertex) for vertex in vertices
        ])

        np.testing.assert_array_equal(remote.configuration.box, origin.configuration.box)
        np.testing.assert_allclose(remote.configuration.box[:3], period / sqrt(72), rtol=1e-7)
        np.testing.assert_array_equal(remote.particles.position, origin.particles.position)
        np.testing.assert_array_equal(remote.particles.image, [[2**28] * 3])
        self.assertEqual(remote.particles.type_shapes, origin.particles.type_shapes)
        shape = np.array(remote.particles.type_shapes[0]["vertices"])
        self.assertAlmostEqual(np.linalg.norm(shape[1] - shape[0]), 1)

    def test_rejects_exactly_singular_periods(self):
        vertices = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
        with self.assertRaisesRegex(ValueError, "invertible period matrix"):
            self.frame([(2, 3, 5), (7, 11, 13), (9, 14, 18)], vertices)
