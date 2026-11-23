module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public section

/-!
# The Chen–Engel–Glotzer regular tetrahedron packing

Coordinates are from Definition 2 and Theorem 1, equations (15)–(16),
of arXiv:1001.0586v3. All lengths are scaled by 160.
-/

namespace PackingCertificate

open Filter MeasureTheory Set
open scoped BigOperators Topology

def motifVertex : Fin 4 → Fin 4 → Fin 3 → ℤ :=
  ![![![320, 320, 320], ![320, -160, -160], ![-160, 320, -160], ![-160, -160, 320]],
    ![![-320, -320, -320], ![320, -160, -160], ![-160, 320, -160], ![-160, -160, 320]],
    ![![134, -157, -343], ![134, 323, 137], ![614, -157, 137], ![614, 323, -343]],
    ![![774, 483, 297], ![134, 323, 137], ![614, -157, 137], ![614, 323, -343]]]

/-- The primitive periods `a+b`, `b+c`, `c+a` in the same units. -/
def periodVector : Fin 3 → Fin 3 → ℤ :=
  ![![384, 576, 192], ![90, 291, 573], ![576, 36, 360]]

/-- Cartesian shift indexed by the three integer lattice coordinates. -/
def periodShift (k : Fin 3 → ℤ) (r : Fin 3) : ℝ :=
  ∑ j : Fin 3, (k j : ℝ) * (periodVector j r : ℝ)

/-- One translated tetrahedron in the periodic packing. -/
def piece (p : Fin 4 × (Fin 3 → ℤ)) : Set (Fin 3 → ℝ) :=
  convexHull ℝ (range fun a => (fun r => (motifVertex p.1 a r : ℝ)) + periodShift p.2)

/-- The motif has a common positive squared length for every edge.
The pieces have disjoint interiors and cover a fraction tending to
`4000/4671` in expanding, origin-centered coordinate cubes. -/
theorem packing_density :
    (∀ i a b : Fin 4, a ≠ b →
      ∑ r : Fin 3, ((motifVertex i a r : ℝ) - (motifVertex i b r : ℝ)) ^ 2 = 460800) ∧
    (Pairwise fun p q => Disjoint (interior (piece p)) (interior (piece q))) ∧
    Tendsto (fun R : ℝ =>
      volume.real ((⋃ p, piece p) ∩ Metric.closedBall 0 R) /
        volume.real (Metric.closedBall (0 : Fin 3 → ℝ) R))
      atTop (𝓝 (4000 / 4671 : ℝ)) := by
  sorry

end PackingCertificate
