import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.LinearAlgebra.CrossProduct

-- Verify the Mathlib declarations available for a periodic packing certificate.
#check Finset.convexHull_eq
#check AffineBasis.interior_convexHull
#check AffineBasis.convexHull_eq_nonneg_coord
#check Real.map_matrix_volume_pi_eq_smul_volume_pi
#check MeasureTheory.IsAddFundamentalDomain.covolume_eq_volume
#check MeasureTheory.IsAddFundamentalDomain.measure_eq
#check crossProduct
#check ZLattice.covolume_eq_det
