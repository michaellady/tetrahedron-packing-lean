module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.LinearAlgebra.CrossProduct

@[expose] public section

-- Verify the Mathlib declarations available for a periodic packing certificate.
#check Finset.convexHull_eq
#check AffineBasis.interior_convexHull
#check AffineBasis.convexHull_eq_nonneg_coord
#check Real.map_matrix_volume_pi_eq_smul_volume_pi
#check MeasureTheory.IsAddFundamentalDomain.covolume_eq_volume
#check MeasureTheory.IsAddFundamentalDomain.measure_eq
#check crossProduct
#check ZLattice.covolume_eq_det
